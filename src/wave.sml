(****************************************************************************)
(********                                                            ********)
(********         The Wave Tactic                                    ********)
(********                                                            ********)
(****************************************************************************)

exception noWave

fun waveTac most l2r rule subg S =
    let val Jthing = if l2r then ?"%Eq J sym%" else ?"%Eq J%"
        val EqB = case ?"%Eq%" of Ref b => b | _ => failwith "bad Eq"
        val HOLE = "x"
        fun switch true (a,b) = (vooWhnf a,b)
          | switch false (a,b) = (vooWhnf b,a)
        fun mkProfs i spot (C,T) =
            case vooWhnf T
              of Bind ((Pi,v),nam,dom,ran) =>
                 let val b = noo (HoleBV,nam) (HOLE,i) ([],dom)
                     val ran' = subst1 (Ref b) ran
                     val spot' = MkApp ((spot,[Ref b]),[prVis v])
                 in  mkProfs (i+1) spot' (b::C,ran')
                 end
               | Bind ((Sig,_),nam,p1,p2) =>
                 let val spot1 = Proj (Fst,spot)
                     val spot2 = Proj (Snd,spot)
                     val (C2,(zap,paz)) = copyCtxt iota C
                     val p2' = zap%>>(subst1 spot1 p2)
                 in  (mkProfs i spot1 (C,p1))@(mkProfs i spot2 (C2,p2))
                 end
               | App ((Ref qb,[Ty,L,R]),_) =>
                 if sameRef qb EqB
                 then let val just = noo ((Let,Def),"just")
                                         ("just",1) ([],spot)
                          val here = noo ((Lda,Hid),"here")
                                         ("here",1) ([],Ty)
                          val (lhs,rhs) = switch l2r (L,R)
                      in  [(just::here::C,CnLst [LabVT (RedPr,lhs,rhs)])]
                      end
                 else []
               | _ => []
        val profs = mkProfs 1 rule ([],type_of_constr rule)
        fun gotit i [] = false
          | gotit i ((j,_)::t) = i=j orelse gotit i t
        fun gotemall (C,_) sbst = vooctxtrec
           {hitBot = const true, hitDom = voocontinue,
            hitVoo = fn _ => fn b => fn _ => fn rect =>
                     case ref_bd b
                       of ((Hole,Def),_,Var ((i,_),_),_) =>
                          gotit i sbst andalso rect ()
                        | _ => rect ()} C
        fun clickDown pat tm =
            let val (P as (pf,paa,pvv)) = parseApp pat
                val (T as (tf,taa,tvv)) = parseApp tm
            in  if sameTerm pf tf then (P,T)
                else
            let val (T as (tf,taa,tvv)) = parseApp (vooWhnf tm)
            in  if sameTerm pf tf then (P,T)
                else raise noWave
            end end
        fun getOne [] term = raise noWave (* do in other order, Conor *)
          | getOne (prof::rest) term =
            let
                val myCache = ref (vooCopy prof)
                fun theRew _ tm =
                   (let val prof = !myCache
                        val pat = case #2 prof
                                    of CnLst [LabVT (_,l,_)] => l
                                     | _ => failwith "oops"
                        val ((pf,paa,pvv),(tf,taa,tvv)) =
                            clickDown pat tm
                        fun doArgs sbst ldas [] _ aa vv =
                           (sbst,ldas,aa,vv)
                          | doArgs sbst ldas (oaa as oah::oat) ovv [] _ =
                            let val e = noo ((Lda,Vis),"") ("eta",1)
                                        ([],type_of_constr (sbst$>>oah))
                            in  doArgs sbst (e::ldas) oaa ovv
                                       [Ref e] [ShowNorm]
                            end
                          | doArgs sbst l (oah::oat) (_::ovt)
                                   (iah::iat) (_::ivt) =
                           (case par_unif sbst (sub sbst oah) (sub sbst iah)
                              of SOME s => doArgs s l oat ovt iat ivt
                               | NONE => raise noWave)
                          | doArgs _ _ _ _ _ _ = raise noWave
                       val (sbst,ldas,aa,vv) = doArgs [] [] paa pvv taa tvv
                   in  if gotemall prof sbst (* not good enough in general *)
                       then ((myCache := (sbst$>>>prof));
                             (Mod (sbst$>>($!(ldas,
                              MkApp ((vid (!myCache) ("here",1),aa),vv))))))
                       else raise noWave
                   end
                   handle noWave => UMod)
            in  case voorewrite theRew term
                  of UMod => getOne rest term
                   | Mod t => (!myCache,t)
            end
        fun doTheWaves most id S = if most<>0 then
            let val b = fetch S id
                val T = case (bCT b)
                          of ([],T) => T
                           | _ => failwith "cannae wave"
            in (let val (stuff,template) = getOne profs T
                    val (just,here,src,tgt) =
                        case stuff
                          of ([just,here],CnLst [LabVT (_,lhs,rhs)]) =>
                             (just,here,lhs,rhs)
                           | _ => failwith "cannae wave"
                    val T = ref_typ here
                    val eqn = noo ((Lda,Vis),"eqn") ("eqn",1)
                              ([],App ((Ref EqB,
                              if l2r then [T,Ref here,tgt]
                                     else [T,tgt,Ref here]),
                                          [NoShow,ShowNorm,ShowNorm]))
                    val phi = ([eqn,here],template)
                    val (X,Y) = switch l2r (src,tgt)
                    val next = noo (HoleBV,ref_nam b) id
                               ([],[(here,tgt)]%>>template)
                    val trick = ([next],App ((Jthing,
                                        [T,X,Y,ref_val just,$!phi,Ref next]),
                                        [NoShow,NoShow,NoShow,
                                         ShowNorm,ShowNorm,ShowNorm]))
                in  doTheWaves (most-1) id ((id \ trick) S)  (* dangerous *)
                end
                handle noWave => S)
            end else S
    in  on S
          [vooattack subg ("zob",1),
           vooIntroTac ("zob",1),
           doTheWaves most ("zob",1),
           prologRetreat subg]
    end

local

  fun addOne (i,t) Y l =
      let fun gotOne [] = false
            | gotOne ((j,_)::t) = if i=j then true else gotOne t
      in  if gotOne l then l else (i,(t,Y))::l
      end

  fun metaVars (Var (X,Y)) l = addOne X Y l
    | metaVars (App ((f,aa),_)) l = metaVars f (foldr metaVars l aa)
    | metaVars (Tuple (t,aa)) l = metaVars t (foldr metaVars l aa)
    | metaVars (LabVT (_,s,t)) l = metaVars t (metaVars s l)
    | metaVars (CnLst aa) l = foldr metaVars l aa
    | metaVars (RedTyp (_,x)) l = metaVars x l
    | metaVars (Case (s,t)) l = metaVars t (metaVars s l)
    | metaVars _ l = []

  fun zappaz [] = ([],[])
    | zappaz ((i,(t,y))::rest) =
      let val b = noo ((Pi,Vis),"ugly") ("vengle",i) ([],y)
      in  ((cons (i,Ref b))**(cons (b,(Var ((i,t),y))))) (zappaz rest)
      end

in

fun legoWave most l2r rule_c =
    let val ((V,T),_) = EvalRefine Synt.type_of_Var (parser_var_pack()) rule_c
        val (zap,paz) = zappaz (metaVars V [])
        val S = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
               [voodom ("goal",1),introall whnf "a" 1,domvoo ("goal",1),
                fn S => zap$>>>S,
                waveTac most l2r (zap$>>V) ("goal",1),
                fn S => paz%>>>S]
    in  vooLegoRefine [("type",1),("blah",1)] S
    end

end