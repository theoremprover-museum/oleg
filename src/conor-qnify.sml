(*******************************************************************)
(*                                                                 *)
(*  The All-New Dependendent Qnify (fortified with Vitamin K)      *)
(*                                                                 *)
(*******************************************************************)
(*
signature CONORQNIFY =
sig
  type cnstr_c
  val cleverClobberFlag : bool ref
  val ClobberTac : cnstr_c -> int -> cnstr_c -> unit
  val ElimTac : cnstr_c -> int -> unit
  val InvertTac : cnstr_c -> int -> unit
  val InitialiseQnify : unit -> unit
  exception noQnify
  val KJunifyTac : int -> unit
end
*)
signature CONORQNIFYNEEDS =
sig
    structure ConorRequire : CONORREQUIRE
(*    structure Voodoo       : VOODOO *)
    structure Namespace : NAMESPACE
    structure Synt : SYNT
    structure Toplevel : TOPLEVEL
    structure Concrete : CONCRETE
    val atoi : string -> int  
    val sameTerm : cnstr->cnstr->bool
    val weakHeadRed : cnstr->cnstr
    sharing type Synt.cnstr_c =     Concrete.cnstr_c
        and type Toplevel.cnstr_c = Concrete.cnstr_c
end

functor ConorQnify ( structure ConorQnifyNeeds : CONORQNIFYNEEDS
                   ) : CONORQNIFY =
struct
  local
      open ConorQnifyNeeds
      open ConorRequire
      open Voodoo
      open Namespace
      open Synt
      open Toplevel
      open Concrete

      exception scarySplice

      fun splice l bum =
          let fun spl1 (l as ((h::t)::_)) =
                  let val cdrs = (map tl l) handle _ => raise scarySplice
                      val spliceTail = spl1 cdrs
                      fun spl2 [] = spliceTail
                        | spl2 ((h::_)::t) = h::(spl2 t)
                        | spl2 _ = raise scarySplice
                  in  spl2 l
                  end
                | spl1 ([]::t) =
                  let fun chk [] = bum
                    | chk ([]::t) = chk t
                    | chk _ = raise scarySplice
                  in  chk t
                  end
                | spl1 [] = bum
          in  spl1 l
          end

      fun filter p =
          let fun f2 [] = ([],[])
                | f2 (h::t) =
                  let val (filt,res) = f2 t
                  in  if p h then (h::filt,res) else (filt,h::res)
                  end
          in  f2
          end

      fun orlist p =
          let fun o2 [] = false
                | o2 (h::t) = p h orelse o2 t
          in  o2
          end

      fun ArgsAndVis ctxt bum =
          let fun av2 [] = bum
                | av2 ((i,(_,v),_,_)::rest) =
                  let val (rs,vs) = av2 rest
                  in  ((Voo i)::rs,
                       ((fn Hid => NoShow | _ => ShowNorm) v)::vs)
                  end
          in  av2 ctxt
          end

      fun vooglue l1 (l2,t) = (l1@l2,t)

      fun voobdep (VBind (_,_,_,v)) = 1+(voobdep v)
        | voobdep _ = 0

      local
          fun pa2 a' v' (VApp ((f,a),v)) = pa2 (a@a') (v@v') f
            | pa2 a  v                 f = (f,a,v)
      in  val vooparseapp = pa2 [] []
      end

      fun flApp ((f,a),v) =
          if a=[] then f else VApp((f,a),v)

      fun vooblat sid T (VApp ((Voo id,blargs),blvis)) =
          if id=sid then voobeta T blargs blvis
          else raise voodoo_no_rewrite
        | vooblat sid T (Voo id) =
          if id=sid then T else raise voodoo_no_rewrite
        | vooblat _ _ _ = raise voodoo_no_rewrite

      fun vooreq tag = voo (#1 (Require tag))

      fun vapparg i v =
          let val (f,a,_) = vooparseapp v
          in  case i
                of 0 => f
                 | n => nth a n handle Nth _ => raise missing_voodoo
          end

      fun voohead (VBind (_,_,_,v)) = voohead v
        | voohead x = #1 (vooparseapp x)

      fun voorename i j (vc,vt) =
          let fun vr2 [] = raise missing_voodoo
                | vr2 ((h as (k,a,b,c))::t) =
                  if i=k then (j,a,b,c)::t
                  else h::(vr2 t)
          in voosub i (Voo j) (vr2 vc,vt)
          end

      fun batchrename s i t j 0 S = S
        | batchrename s i t j n S =
          batchrename s (i+1) t (j+1) (n-1)
                      (voorename (s,i) (t,j) S)

      fun SNs 0 = []
        | SNs i = ShowNorm::(SNs (i-1))


(* parselim splits up elimination-style rules according to the pattern

        all pi,xi    (pi: parameters, xi: prior indices)
        all Phii     (Phii: schemata)
        all subgoali (subgoali: case rules of form stuff->Phij things)
        all yi       (yi: posterior indices)
          Phik xs ys (a schema applied to some index variables)

   Typically, Phik can be inferred by beta0, giving rise to a convenient
   form of rule application, essentially implemented by elimPlan. *)

      fun parselim ert =
          let val depth = voobdep ert
              val s1 = introvool ["d"] 1 depth ([],ert) (* d for dunno *)

              val (phind,phargids) =
                  (fn (Voo (_,i),a,_) =>
                      (i,map (fn (Voo v) => v
                               | _ => raise missing_voodoo) a)
                    | _ => raise missing_voodoo) (vooparseapp (#2 s1))
              val phid = ("Phi",phind)
              val s2 = voorename ("d",phind) phid s1

              fun miny [] = depth+1
                | miny ((_,i)::t) =
                  let val j = miny t
                  in  if i>phind andalso i<j then i else j
                  end
              val ystart = miny phargids
              val s3 = batchrename "d" ystart "y" 1 (depth+1-ystart) s2

              fun spotxs [] S = S
                | spotxs ((_,i)::t) S =
                  if i<phind then spotxs t (voorename ("d",i) ("x",i) S)
                  else spotxs t S
              val s4 = spotxs phargids s3

              fun getem [] l = l
                | getem ((("d",i),_,_,v)::t) l =
                  if i>phind
                  then case (voohead v)
                         of (Voo ("d",i)) => if member i l then getem t l
                                             else getem t (i::l)
                          | _ => getem t l
                  else getem t l
                | getem (_::t) l = getem t l
              val dsforPhis = getem (#1 s4) []
              val s5 = foldr (fn i => voorename ("d",i) ("Phi",i)) s4 dsforPhis

              fun renumber (ind as (pi,xi,Phii,sgi))
                           ((h as (i as (s,_),bv,n,ty))::t,tail) =
                  let fun gloo i' ind' =
                          let val (c,v) =
                              renumber ind' (voosub i (Voo i') (t,tail))
                          in  ((i',bv,n,ty)::c,v)
                          end
                  in  case s
                        of "x"   => gloo ("x",xi) (pi,xi+1,Phii,sgi)
                         | "Phi" => gloo ("Phi",Phii) (pi,xi,Phii+1,sgi)
                         | "d"   => if Phii=1 (* ie before first Phi *)
                                    then gloo ("p",pi) (pi+1,xi,Phii,sgi)
                                    else gloo ("subgoal",sgi)
                                              (pi,xi,Phii,sgi+1)
                         | "y"   => let val (c,v) = renumber ind (t,tail)
                                    in  (h::c,v)
                                    end
                         | _ => raise RequireFailure
                  end
                | renumber _ ([],t) = ([],t)
              val s6 = renumber (1,1,1,1) s5
          in  s6
          end



      fun newAge () = case (getNamespace ())
                       of (h::_) => ref_ts h
                        | _ => raise RequireFailure

      fun minTS [] = 1+(newAge())
        | minTS ((h,_)::t) =
          let val ts = minTS t
          in  if h<ts then h else ts
          end

      fun checkLets ts =
          let fun bof [] = ()
                | bof (h::t) =
                  if (ref_ts h)<=ts then ()
                  else if (ref_kind h)=Bnd andalso (ref_bind h)=Let
                           then print "Warning: abstracting through a let!\n"
                       else bof t
          in  bof (getNamespace ())
          end

      fun refAbstract alist S =
          let val _ = checkLets (minTS alist)
              fun blam ts vid (VRef b) =
                  if ts=(ref_ts b) then Voo vid else raise voodoo_no_rewrite
                | blam _ _ _ = raise voodoo_no_rewrite
              fun dobiz [] = S
                | dobiz ((ts,vid)::t) = voolift (voorewrite (blam ts vid))
                                        (dobiz t)
          in  dobiz alist
          end

      fun choppec (S as (c,t)) =
          let val slug = ref c
              fun peel sl ((h as((s,_),_,_,_))::t) =
                  if member s sl then ((slug:=t);(h::(peel sl t)))
                  else []
                | peel _ _ = []
              val pxs = peel ["p","x"] (!slug)
              val Phis = peel ["Phi"] (!slug)
              val subgs = peel ["subgoal"] (!slug)
              val (i,ty,a,v) =
                 (fn (Voo (p as ("Phi",i)),a,v) =>
                     (i,#4 (fetch p S),a,v)
                   | _ => raise missing_voodoo) (vooparseapp t)
          in  (pxs,Phis,subgs,!slug,i,ty,a,v)
          end

      fun mkList f b e = if b>e then []
                         else (f b)::(mkList f (b+1) e)

      fun mkVl s = mkList (fn i => Voo (s,i))

      fun vooPiToLda (i,(Pi,v),s,u) = (i,(Lda,v),s,u)
        | vooPiToLda x = x
      fun vooPiToLdaElideName (i,(Pi,v),s,u) = (i,(Lda,v),"",u)
        | vooPiToLdaElideName x = x
      fun vooPiToLdaHide (i,(Pi,v),s,u) = (i,(Lda,Hid),"",u)
        | vooPiToLdaHide x = x

      fun freshName "" i cxt = freshName "vlart" i cxt
        | freshName s 0 cxt =
          if defined s cxt then freshName s 1 cxt else s
        | freshName s i cxt =
          let val s' = s^"_"^(string_of_num i)
          in  if defined s' cxt then freshName s (i+1) cxt else s'
          end

      fun exCon ([],v) c = (c,[],[],v)
        | exCon (((id,bv,nam,vty)::t),v) c =
          let val name = freshName nam 0 c
              val ty = unvoo vty
              val ki = #2 (fEvalCxt c (unEval ty))
              val c' = extendCxt Bnd bv (UnFroz,Local) [] name (ty,ki) c
              val bd = hd c'
              val ts = ref_ts bd
              val S' = voosub id (VRef bd) (t,v)
              val (c'',al,la,v'') = exCon S' c'
          in  (c'',(ts,id)::al,(id,bd)::la,v'')
          end

      fun voowrap ctxt frontEnd cnstrFn backEnd arg =
          let val oldNSP = getNamespace ()
          in  let val (NS,reabsAL,unabsAL,_) = exCon (ctxt,VProp) oldNSP
                  val _ = putNamespace NS  (* dodgy or what? *)
                  fun malb (Voo id) =
                     (VRef (assoc id unabsAL)
                      handle Assoc => raise voodoo_no_rewrite)
                    | malb _ = raise voodoo_no_rewrite
                  val erotser = voorewrite malb
                  val fnReturn = cnstrFn (frontEnd erotser arg)
                  fun blam (VRef b) =
                     (Voo (assoc (ref_ts b) reabsAL)
                      handle Assoc => raise voodoo_no_rewrite)
                    | blam _ = raise voodoo_no_rewrite
                  val restore = voorewrite blam
                  val result = backEnd restore fnReturn
                  val _ = putNamespace oldNSP
              in  result
              end
              handle x => ((putNamespace oldNSP);
                           (raise x))
          end

      fun construe rew v = unvoo (rew v)
      fun review   rew c = rew (voo c)
      fun review2  rew (c,d) = (rew (voo c),rew (voo d))

      fun voowrapc2c ctxt c2c = voowrap ctxt construe c2c review

      fun voosynth ctxt =
          let fun dorew rew (f,a) = (rew f,map rew a)
              fun middle (f,a) =
                  let val (Vf,Tf) = fEval (unEval (unvoo f))
                      val pvp = parser_var_pack ()
                      fun inferArgs sbst Vf (Bind ((Pi,v),_,dom,rng))
                                            (ah::at) =
                          let val (Va,Ta) =
                                  case ah
                                    of Voo _ => (pvp dom,dom)
                                     | _ => fEval (unEval (unvoo ah))
                              val sbst = case par_unif sbst Ta dom
                                           of SOME s => s
                                            | NONE => raise missing_voodoo
                              val pv = case v
                                         of Vis => ShowNorm
                                          | _ => ShowForce
                              val Vf = sub sbst (MkApp((Vf,[Va]),[pv]))
                              val Tf = whnf (sub sbst (subst1 Va rng))
                          in  inferArgs sbst Vf Tf at
                          end
                        | inferArgs sbst Vf _ _ = vooparseapp (voo Vf)
                      val (f,a,_) = inferArgs [] Vf (whnf Tf) a
                  in  (f,a)
                  end
          in  voowrap ctxt dorew middle dorew
          end

      fun voopure v ex = voorewrite (fn (VVar _) => raise ex
                                     | _ => raise voodoo_no_rewrite) v

      fun vooctxtelide id [] = raise missing_voodoo
        | vooctxtelide id ((h as (jd,_,_,_))::t) =
          if id=jd then t else h::(vooctxtelide id t)

      fun triangularise _ [] = []
        | triangularise ldas ((i,(Pi,v),s,t)::rest) =
          (vooeta (outrovoo (ldas,t)))::
          (triangularise (ldas@[(i,(Lda,Vis),s,t)]) rest)
        | triangularise _ _ = raise RequireFailure

      fun build_equations name index As ts hs =
          let val veq = vooreq ["Eq"]
              fun be2 _ _ _ _ _ _ [] [] [] = []
                | be2 i j rs vs ys us (hA::tA) (hs::ts) (ht::tt) =
                  let val rs' = rs@[hA,hs,ht,Voo (name,i)]
                      val vs' = NoShow::NoShow::NoShow::ShowNorm::vs (*crafty*)
                      val ys' = ys@[ht]
                      val us' = ShowNorm::us
                      val eqty = case j of 0 => hA | _ => VApp ((hA,ys),us)
                      val eqlh =
                          case j
                           of 0 => hs
                            | _ => let val vsubRef = vooreq
                                           ["dep","subst",string_of_num j]
                                   in  VApp ((vsubRef,rs@[hA,hs]),vs)
                                   end (* and that's why it's crafty ^^ *)
                      val eqblah = ((name,i),(Pi,Vis),"",
                                    VApp ((veq,[eqty,eqlh,ht]),
                                             [NoShow,ShowNorm,ShowNorm]))
                  in  eqblah::(be2 (i+1) (j+1) rs' vs' ys' us' tA ts tt)
                  end
                | be2 _ _ _ _ _ _ _ _ _ = raise RequireFailure
          in  be2 index 0 [] [ShowNorm,ShowNorm] [] [] As ts hs
          end (* subst apps always end with 2 ShowNorms... crafty! *)

      fun linearTriangular [] = ([],[])
        | linearTriangular (l as ((i,_,_,v)::t)) =
          if orlist (fn (_,_,_,y) => voooccur i y) t
          then ([],triangularise [] l)
          else let val (lin,tri) = linearTriangular t
               in (v::lin,tri)
               end

      fun buildLinTriEqs name index (lin,tri) ls rs =
          let val veq = vooreq ["Eq"]
              fun blte1 i [] ls rs = build_equations name i tri ls rs
                | blte1 i (Th::Tt) (lh::lt) (rh::rt) =
                  ((name,i),(Pi,Vis),"",
                   VApp ((veq,[Th,lh,rh]),[NoShow,ShowNorm,ShowNorm]))::
                  (blte1 (i+1) Tt lt rt)
                | blte1 _ _ _ _ = raise RequireFailure
          in  blte1 index lin ls rs
          end

      fun voosolve id sol S = elide id (voosub id sol S)

      fun promoteEquations id S =
          let val (_,bv,nam,subgoal) = fetch id S
              val veq = vooreq ["Eq"]
              val eqts = case veq
                           of (VRef b) => ref_ts b
                            | _ => failwith "odd equality"
              fun doIntros pi qi (S as (_,t)) =
                  case t
                    of VBind ((Pi,_),_,
                        VApp ((VRef b,[_,_,_]),_),_) =>
                       if (ref_ts b)=eqts
                       then doIntros pi (qi+1) (introvool ["equation"] qi 1 S)
                       else doIntros (pi+1) qi (introvool ["premise"] pi 1 S)
                     | VBind ((Pi,_),_,_,_) =>
                       doIntros (pi+1) qi (introvool ["premise"] pi 1 S)
                     | _ => S
              val (pref,tail) = doIntros 1 1 ([],subgoal)
              val (ps,qs) = filter
                            (fn (("premise",_),_,_,_) => true | _ => false)
              (*mind 'em*)  pref
              val (newPref,_) = foldr (fn e => shove e ("bogus",0))
                                (ps,tail) qs
              val newSubgType = outrovoo (newPref,tail)
              val (rs,vs) = ArgsAndVis newPref ([],[])
              val solver = vooeta                                      (
                  outrovoo (map vooPiToLda pref,VApp ((Voo id,rs),vs)) )
              val S = swap (id,bv,nam,newSubgType) (voosub id solver S)
          in  S
          end

      fun genova ctxt id S =
          let val (_,bv,nam,oldType) = fetch id S
              val newType = outrovoo (ctxt,oldType)
              val (rs,vs) = ArgsAndVis ctxt ([],[])
              val repIdBy = flApp ((Voo id,rs),vs)
          in  swap (id,bv,nam,newType) (
              voosub id repIdBy S      )
          end

      fun elimClobberPlan genFlag otherStuff rule
                         (S as (goalPref,goalTail)) target =
          let val (goalPref,goalTail,target) =
                  case introvool ["q"] 1 (length goalPref)
                       ([],outrovoo (goalPref,
                                     VLabVT (Name "bogus",goalTail,target)))
                    of (goalPref,VLabVT (Name "bogus",goalTail,target)) =>
                       (goalPref,goalTail,target)
                     | _ => bug "bad Clobbering"
              (* make sure these bits are called q *)
              val veqr = vooreq ["Eq","refl"]
              val veq = vooreq ["Eq"]
              val vrt = voowrap otherStuff construe type_of_constr review rule
              val (elimPref,elimTail) = parselim vrt
              val (pxs,Phis,subgs,ys,Phind,PhiType,PhiArgs,PhiVis) =
                  choppec (elimPref,elimTail)

              (* We place the target in the targetter and
                 infer the rest of the indices, we hope *)

              fun placeTarget [] = ([],true)
                | placeTarget ((id as (s,_),(Pi,v),_,_)::pet) =
                  let val (bum,targetting) = placeTarget pet
                  in  if targetting
                      then if s="x" orelse s="y" orelse s="p"
                           then (target::bum,false)
                           else ((Voo id)::bum,true)
                      else ((Voo id)::bum,false)
                  end
                | placeTarget _ = raise missing_voodoo

              val (argsGetTarget,_) = placeTarget elimPref
              val (_,infArgs) =
                  voosynth (otherStuff@goalPref) (rule,argsGetTarget)
              (* infArgs may be prefixed with args supplied to the rule *)
              val infArgs = List.nthtail (infArgs,
                              (length infArgs)-(length elimPref))
              val infAList = ListUtil.zip (map (#1) elimPref,infArgs)

              val PhiList = foldr (fn Voo id => (fn l => id::l)
                                    | _ => (fn l => l)) [] PhiArgs
              val (indices,_) = filter (fn (id,_,_,_) =>
                                           member id PhiList) elimPref
              val indexVars = map (Voo o (#1)) indices
              val indexArgs = map (fn (id,_,_,_) => assoc id infAList)
                              indices

              (* We need to grab the goalPref elements which are
                 going to be inside Phi: these are the ones on which
                 the ps do not depend; the others we then pick up,
                 in order to generalise the subgoals *)

              fun chopList _ [] = []
                | chopList [] ctxt = ctxt
                | chopList (h::t) ctxt =
                 (let val (_,_,_,v) = fetch h (ctxt,VProp)
                      val ctxt = vooctxtelide h ctxt
                  in chopList ((dep1l v)@t) ctxt
                  end
                  handle missing_voodoo =>
                  chopList t ctxt)
              val purEx = Failure "Clobber cannot infer an argument"
              fun getArgs s =
                  foldr (fn (id as (s',i),_,_,_) => fn rest =>
                            if s=s'
                            then (voopure (assoc id infAList) purEx)::rest
                            else rest)
                        [] pxs
              val pargs = getArgs "p"
              val xargs = getArgs "x"
              fun paramSpot [] pref = pref
                | paramSpot (pxah::pxat) pref =
                  paramSpot pxat (chopList (dep1l pxah) pref)
              fun idThere id ctxt =
                 (let val _ = fetch id (ctxt,VProp)
                  in  true
                  end
                  handle missing_voodoo => false)
              val reducedPref = paramSpot pargs goalPref
(**)
              val (_,genSubsOver) = filter
                                    (fn (id,_,_,_) => idThere id reducedPref)
                                    goalPref
(**)
              
              (* We need to chop the goalPref into the intros and ldas *)
              val pxDeps = paramSpot (pargs@xargs) goalPref
              fun findPrefix comp [] = ([],[],false)
                | findPrefix comp ((h as (hid,_,_,_))::t) =
                  let val (pref,suff,b) = findPrefix comp t
                  in  if b orelse (not (idThere hid comp))
                      then (h::pref,suff,true)
                      else (pref,h::suff,false)
                  end
              val applyParams =
                  voorewrite (fn (Voo ("p",i)) => assoc ("p",i) infAList
                               | _ => raise voodoo_no_rewrite)
              val (introThese,lambdaThese,_) = findPrefix pxDeps goalPref

              (* We compute the equations for the indices.*)
              val linTri = linearTriangular indices
              val eqns = buildLinTriEqs "eqn" 1 linTri indexVars indexArgs

              (* We reduce this collection of equations by removing
                 those involving fresh variables, possibly
                 generalising those variables, hence requiring
                 coercions in the goal. *)
              val beforeGoal = (reducedPref,goalTail)
              fun solveSome i [] _ eqS goalS = ([],eqS,goalS)
                | solveSome i ((Voo id)::t) ((h as (iid,bv,_,ity))::itl)
                            eqS goalS =
                  if idThere id (#1 goalS)
                  then (* replace iid by id, coerce id, solve eqn *)
                  let val eqS = voosub iid (Voo id) eqS
                      val (qid,_,_,qty) = fetch ("eqn",i) eqS
                      val (lty,coercedId) =
                          case qty
                            of VApp ((_,[lty,lhs,_]),_) => (lty,lhs)
                             | _ => raise missing_voodoo
                      val itl = #1 (voosub iid (Voo id) (itl,VProp))
                      val goalS = voosolve id coercedId goalS
                      val eqS = voosolve qid (VApp ((veqr,[lty,coercedId]),
                                                 [NoShow,ShowNorm]))    (
                                voosub id coercedId                    (
                                eqS                                    ))
                      val (itl,eqS,goalS) = solveSome (i+1) t itl eqS goalS
                  in  ((id,bv,"",ity)::itl,eqS,goalS)
                  end
                  else
                  let val (itl,eqS,goalS) = solveSome (i+1) t itl eqS goalS
                  in  (h::itl,eqS,goalS)
                  end
                | solveSome i (_::t) (h::itl) eqS goalS =
                  let val (itl,eqS,goalS) = solveSome (i+1) t itl eqS goalS
                  in  (h::itl,eqS,goalS)
                  end
                | solveSome _ _ _ _ _ = raise missing_voodoo
              val (newInds,(newEqs,_),(newPref,newGoalTail)) =
                  solveSome 1 indexArgs indices (eqns,VProp) beforeGoal



              (* We construct Phi;
                 then we modify the subgoals accordingly *)
              val protoPhi = foldr (fn e => shove e ("bogus",0))
                             (newPref,newGoalTail) newEqs
              val Phi = applyParams (
                  vooeta (outrovoo (map vooPiToLda newInds,outrovoo protoPhi)))
              val doTheBiz = applyParams o
                            (voorewrite (vooblat ("Phi",Phind) Phi))
              val (RealPhis,_) = elide ("Phi",Phind)
                                (voolift doTheBiz (Phis,VProp))
              val (NewSubgs,_) = voolift doTheBiz (subgs,VProp)

              (* We optimise the subgoals for unification *)
              val trickSubgs = VCnLst (map (fn x => Voo (#1 x)) subgs)
              val trickState = (NewSubgs,trickSubgs)
              (* note the flag controls the genova move *)
              val trick =
                  if genFlag
                  then fn id => fn S => promoteEquations id
                                       (genova genSubsOver id S)
                  else promoteEquations
              val (RealSubgs,trickSolvers) =
                  foldr (fn (id,_,_,_) => fn S => trick id S)
                        trickState subgs
              val elimSubgs = case trickSolvers
                                of VCnLst l => l
                                 | _ => failwith "weird equation happening"

              (* We build the plan *)
              (* args to elim *)
              fun mkarg (("Phi",i),_,_,_) =
                  if i=Phind then Phi else Voo ("Phi",i)
                | mkarg (("subgoal",i),_,_,_) = nth elimSubgs i
                | mkarg (("eqn",_),_,_,VApp ((_,[t,_,r]),_)) =
                  VApp ((veqr,[t,r]),[NoShow,ShowNorm])
                | mkarg (("q",i),_,_,_) = Voo ("q",i)
                | mkarg (id,_,_,_) = assoc id infAList
              val elimArgPlan = pxs@Phis@subgs@ys@(#1 protoPhi)
              val elimArgs = map (applyParams o mkarg) elimArgPlan
              val elimVis = map (fn (_,(_,Vis),_,_) => ShowNorm
                                  | (_,(_,_),_,_) => NoShow)
                                elimArgPlan
              val thePlan =
                  (if genFlag then [] else introThese,
                   RealPhis,
                   RealSubgs,
                   if genFlag then (introThese@lambdaThese)
                              else lambdaThese,
                   VApp ((rule,elimArgs),elimVis))
          in  thePlan
          end

      fun mapAndApp f [] [] = []
        | mapAndApp f [] (h::t) = mapAndApp f h t
        | mapAndApp f (h::t) l = (f h)::(mapAndApp f t l)

      fun elimClobber otherStuff appliedRule S target =
          let val (introThese,RealPhis,RealSubgs,lambdaThese,theTrick) =
              elimClobberPlan false otherStuff appliedRule S target
              val introThese = map vooPiToLda introThese
              val prefix = mapAndApp vooPiToLda []
                           [RealPhis,RealSubgs,lambdaThese]
          in  (introThese,outrovoo (prefix,theTrick))
          end

      fun elimClobberGen otherStuff appliedRule S target =
          let val (introThese,RealPhis,RealSubgs,lambdaThese,theTrick) =
              elimClobberPlan true otherStuff appliedRule S target
              val introThese = map vooPiToLda introThese
              val prefix = mapAndApp vooPiToLda []
                           [RealPhis,RealSubgs,lambdaThese]
          in  (introThese,outrovoo (prefix,theTrick))
          end

      exception noQnify

      fun vnamdepts (VRef (ref (Bd {deps=cl,
                             bd=(_,s,_,_),
                             ts=t,...}))) = (s,cl,t)
        | vnamdepts _ = raise noQnify

      fun howManyJecs conName typeName =
          let val params = #1 (choppec (parselim (voo (#2 (Require
                                                [typeName,"cases"])))))
              val rawArgs = voobdep (voo (#2 (fEval (Ref_c conName))))
          in  rawArgs-(length params)
          end

      fun cons1 h (a,b) = (h::a,b)

      fun ctxtSplit id [] = raise missing_voodoo
        | ctxtSplit id ((h as (jd,_,_,_))::t) =
          if id=jd then ([],t) else cons1 h (ctxtSplit id t)

      fun KorJ tag nIn targ goal =
          let val (fore,aft) = introvool ["gen"] 1 nIn ([],outrovoo goal)
              val k = targ-nIn
              val goal = introvool ["q"] 1 k ([],aft)
              val (_,_,subGoals,lambdaThese,theTrick) =
                  elimClobberPlan true fore (vooreq tag) goal (Voo ("q",k))
              val solveGoal =
                  vooeta (outrovoo (map vooPiToLda lambdaThese,theTrick))
              val (P,T) = genova fore ("subgoal",1) (subGoals,solveGoal)
              val T = outrovoo (map vooPiToLda fore,T)
          in  (0,(P,T))
          end      

      fun vooK id (T,L,R) goal =
         (let val _ =
                  if voowrap (#1 (ctxtSplit id (#1 goal)))
                     (fn rew => fn (u,v) => (unvoo (rew u),unvoo (rew v)))
                     (fn (x,y) => sameTerm x y)
                     (fn _ => fn b => b)
                     (L,R) then () else raise noQnify
              val i = (#2 id)
          in  KorJ ["Eq","K"] (i-1) i goal
          end
          handle _ => raise noQnify)

      fun vooJ (id:voolabel) (T,L,R) goal =
         (let val (Rid,i) = case R
                              of Voo (Rid as ("q",i)) => (Rid,i)
                               | _ => raise noQnify
              val _ = if (voooccur Rid L) then raise noQnify
                      else case L
                             of Voo ("q",j) =>
                                if i<j then raise noQnify else ()
                              | _ => ()
          in  KorJ ["Eq","J"] (i-1) (#2 id) goal
          end
          handle _ => raise noQnify)

      fun vooJsym (id:voolabel) (T,L,R) goal =
         (let val (Lid,i) = case L
                              of Voo (Lid as ("q",i)) => (Lid,i)
                               | _ => raise noQnify
              val _ = if (voooccur Lid R) then raise noQnify
                      else case R
                             of Voo ("q",j) =>
                                if i<j then raise noQnify else ()
                              | _ => ()
          in  KorJ ["Eq","J","sym"] (i-1) (#2 id) goal
          end
          handle _ => raise noQnify)

      fun vooRigidRigid id (T,L,R) (goalP,goalT) =
         (let val (fT,aT,vT) = vooparseapp T
              val (fL,_,_) = vooparseapp L
              val (fR,_,_) = vooparseapp R
              val (nT,cT,_ ) = vnamdepts fT
              val (nL,_ ,_ ) = vnamdepts fL
              val (nR,_ ,_ ) = vnamdepts fR
              val _ = if      (member nL cT)
                      andalso (member nR cT)
                      then ()
                      else raise noQnify
              val (no_conf,itsType) = Require [nT,"no","confusion"]
              val vnc = voo no_conf
              val vitsty = voo itsType
              fun cutup [] = raise noQnify
                | cutup ((h as (jd,_,_,_))::t) =
                  if jd=id then ([h],(vooPiToLda h)::t)
                  else let val (f,b) = cutup t
                       in  (h::f,b)
                       end
              val (front,back) = cutup goalP
              val Psi = outrovoo (back,goalT)
              val dep = (voobdep vitsty)
              val priors = (mkVl "bog" 1 (dep-2))@[Voo id,Psi]
              val (_,v) = ArgsAndVis
                          (#1 (introvool ["splat"] 1 dep ([],vitsty)))
                          ([],[])
              val (f,a) = voosynth front (vnc,priors)
              val trick = VApp ((f,a),v)
              val hnfTy = voowrap front construe (whnf o type_of_constr)
                                  review trick
              val (newSubg,newTail) = introvool ["subgoal"] 1 1 ([],hnfTy)
              val trickApp = flApp ((trick,[Voo ("subgoal",1)]),[NoShow])
          in  if nL=nR
              then (* it's injectivity *)
              let val allBut = vooctxtelide id front
                  val nearly = (newSubg,trickApp)
                  val (subgs,protoPf) =
                      foldr (fn (id,_,_,_) => fn S =>
                                promoteEquations id 
                                (genova allBut id S))
                            nearly newSubg
                  val theProof = outrovoo (map vooPiToLda front,protoPf)
                  val thePlan = (subgs,theProof)
              in  (howManyJecs nL nT,thePlan)
              end
              else (* it's conflict *)
              let val nearly =
                      voosub ("subgoal",1) (voobeta Psi [Voo id] [ShowNorm])
                      (map vooPiToLda front,trickApp)
              in  (0,([],outrovoo nearly))
              end
          end
          handle _ => raise noQnify)

      val voonifyTacs = ref [vooK,vooJ,vooJsym,vooRigidRigid]

      fun vootryTacs id bits G =
          let fun try [] = raise noQnify
                | try (h::t) = h id bits G
                               handle noQnify => try t
          in  try (!voonifyTacs)
          end

      local
          val protCounter = ref 0
          fun introList [] S = S
            | introList ((s,i)::t) S =
              introList t (introvool [s] i 1 S)
      in  fun vooprotect (P:vooctxt,T) =
              let val oldNames = map (#1) P
                  val addOn = length P
                  val old = !protCounter
                  val _ = protCounter := old+addOn
                  val (P,T) = introvool ["protect"] old addOn
                              ([],outrovoo (P,T))
                  val newNames = map (#1) P
              in  (ListUtil.zip (newNames,oldNames),(P,T))
              end
          fun voounprotect alist (S as (P,T)) =
              introList (map (fn (id,_,_,_) =>
                                 assoc id alist
                                 handle Assoc => id) P) 
                        ([],outrovoo S)
      end

      fun app1 l (x,y) = (l@x,y)

      local
          val eqBd = ref (Bd {kind=Bnd,ts=0,frz=ref UnFroz,param=Local,deps=[],
                              bd=((Pi,Vis),"bogus",Bot,Bot)})
          val voowh = voo o weakHeadRed o unvoo
          fun voodointros n (gP,gT) =
              let val (v,s,h,t) =
                      case voowh gT
                        of VBind ((Pi,v),s,h,t) => (v,s,h,t)
                         | _ => raise noQnify
                  val h = voowh h
                  val G = introvool ["q"] n 1 (gP,VBind ((Pi,v),s,h,t))
                  val qn = ("q",n)
              in (case h
                    of VApp ((VRef q',[T,L,R]),_) =>
                       if sameRef q' eqBd
                       then
                      (let val (id,bits,goal) =
                               (qn,(voowh T,voowh L,voowh R),G)
                       in  vootryTacs id bits goal
                       end
                       handle noQnify => raise Match)
                       else raise Match
                     | _ => raise Match)
                  handle Match =>
                  voowrap [last (#1 G)]
                          (fn rew => fn (P,T) => (P,rew T))
                          (voodointros (n+1))
                          (fn rew => fn (n,G) => (n,voolift rew G))
                          G
              end
          fun dovoonify 0 goal = ([(("subgoal",1),(Pi,Vis),"",goal)],
                                  Voo ("subgoal",1))
            | dovoonify n goal =
             (let val (nNew,(subGoals,trick)) = voodointros 1 ([],goal)
              in  case subGoals
                    of [] => ([],trick) (* we won *)
                     | [(sid,_,_,subgoal)] => (* 'nother go, maybe *)
                       let val n = if n<0 then n
                                    else n-1+nNew
                           val (S,T) = dovoonify n subgoal
                       in  (S,voorewrite (vooblat sid T) trick)
                       end
                     | _ => bug "more than one subgoal in voonify"
              end
              handle noQnify => dovoonify 0 goal)
      in  fun voonify n id (S as (SP,ST)) =
              let val (protectData,S as (SP,stuff)) =
                      vooprotect (SP,VCnLst [ST,Voo id])
                  val (ST,id) = case stuff
                                  of VCnLst [ST,Voo id] => (ST,id)
                                   | _ => bug "protection racket"
                  val _ = eqBd :=(case (#1 (Require ["Eq"]))
                                    of Ref b => !b
                                     | _ => raise noQnify)
                  val (fore,aft) = ctxtSplit id SP
                  val (_,bv,nam,subGoal) = fetch id S
                  val (subgS,trick) = 
                      voowrap fore (fn rew => rew) (dovoonify n) voolift 
                              subGoal
              in  voounprotect protectData
                 (case subgS
                    of [] =>
                       let val rew = voorewrite (vooblat id trick)
                       in  app1 fore (voolift rew (aft,ST))
                       end
                     | [(sid,_,_,subgtype)] =>
                       let val rew = voorewrite (vooblat id trick)
                       in  voorename sid id
                          (app1 (fore@[(sid,bv,nam,subgtype)])
                                (voolift rew (aft,rew ST)))
                       end
                     | _ => bug "more than one subgoal in voonify")
              end
      end

      fun elimClobberClever otherStuff appliedRule S target =
          let val (_,RealPhis,RealSubgs,lambdaThese,theTrick) =
              elimClobberPlan true otherStuff appliedRule S target
              val prefix = mapAndApp vooPiToLda []
                           [RealPhis,RealSubgs,lambdaThese]
              val planA = (prefix,theTrick)
              val planB = foldr (fn (id,_,_,_) => fn S =>
                                 voonify (~1) id S)
                                planA RealSubgs
          in  ([],outrovoo planB)
          end

      fun applyPlan (introThese,refineThis) =
          let val introThings = map (fn (_,_,s,_) => "fix_"^s) introThese
              val _ = case introThings
                        of [] => ()
                         | _ => Intros (~9999) false introThings
              val vIds = map (fn (i,_,_,_) => i) introThese
              fun inRef [] _ y = y
                | inRef (h::t) (hb::tb) y = inRef t tb ((VRef hb)::y)
                | inRef _ _ _ = failwith "intros did something odd"
              val AList = ListUtil.zip (vIds,
                                        inRef vIds (getNamespace()) [])
              fun blat (Voo id) =
                 (assoc id AList
                  handle Assoc => raise voodoo_no_rewrite)
                | blat _ = raise voodoo_no_rewrite
              val refineThis = vooeta refineThis
              val refineThang = unvoo (voorewrite blat refineThis)
          in  Refine (~9999) 0 (unEval refineThang)
          end

      fun voorelabel alist (C,T) =
          let fun vr2 (Voo (s,i)) =
                 (Voo (assoc s alist,i)
                  handle Assoc => raise voodoo_no_rewrite)
                | vr2 _ = raise voodoo_no_rewrite
              fun vr3 (B as ((s,i),x,y,z)) =
                 (((assoc s alist,i),x,y,z)
                  handle Assoc => B)
          in  voolift (voorewrite vr2)
              (map vr3 C,T)
          end

      fun glueElim frontElim subg pred backElim =
          let val glueRL = [("p","a"),("x","u"),("Phi","Psi"),
                            ("subgoal","rule"),("y","v")]
              val vFrontRule = voorelabel glueRL
                               (parselim (voo (type_of_constr frontElim)))
              val theSubg = fetch ("rule",subg) vFrontRule
              fun voostripPis (VBind (_,_,_,ty)) = voostripPis ty
                | voostripPis x = x
              fun parsubg s p i (S as (ctx,tail)) =
                  case tail
                    of VBind ((Pi,_),_,ty,_) =>
                       let val (f,a,v) = vooparseapp (voostripPis ty)
                       in  case f
                             of Voo (s',_) =>
                                if s=s'
                                then parsubg s p (i+1)
                                     (introvool ["iter"] i 1 S)
                                else parsubg s (p+1) i
                                     (introvool ["pred"] p 1 S)
                              | _ =>
                                parsubg s (p+1) i (introvool ["pred"] p 1 S)
                       end
                     | _ => S
              val (parsedPref,parsedTail) = parsubg "Psi" 1 1 ([],#4 theSubg)
              fun outTo id ([],T) = ([],T)
                | outTo id ((H as (id',_,_,_))::C,T) =
                  if id=id' then ([H],outrovoo (C,T))
                  else let val (C,T) = outTo id (C,T)
                       in  (H::C,T)
                       end

              (* first we select the relevant predecessor of the
                 front rule and clobber it with the back rule *)
              (* keeping it tidylike, we want to shuffle out of the
                 way those things not involving the pred *)

              val depsLess = deple parsedPref ("pred",pred)
              fun findRest l [] = l
                | findRest l ((id,_,_,ty)::t) =
                  if voofold false
                             (fn i => member i l)
                             (fn true => (fn _ => true)
                               | _    => (fn x => x))
                             ty
                  then findRest (id::l) t
                  else findRest l t
              val keepThese = findRest depsLess parsedPref
              val (keepPref,shuffPref) =
                  filter (fn (id,_,_,_) => member id keepThese) parsedPref
              fun protectNames i [] S = ([],S)
                | protectNames i ((id,bv,_,ty)::t) S =
                  let val (t,_) = voosub id (Voo ("z",i)) (t,VProp)
                      val S = voosub id (Voo ("z",i)) S
                      val (t,S) = protectNames (i+1) t S
                  in  ((("z",i),bv,"",ty)::t,S)
                  end
              val (shuffPref,(keepPref,parsedTail)) =
                  protectNames 1 shuffPref (keepPref,parsedTail)
              val readyToClobber = outTo ("pred",pred) (keepPref,parsedTail)
              val otherStuff = (#1 (outTo ("Psi",1) vFrontRule))@shuffPref
              val (_,sparePhis,subgoals,clobberIts,_) =
                  elimClobberPlan true
                  otherStuff (voo backElim) readyToClobber (Voo ("pred",pred))

              (* second we reduce equations wherever we can *)
              val stuff = otherStuff@sparePhis
              fun mangleSubg i S =
                  let val S = voonify (~1) i S
                  in  let val (_,bv,nam,sty) = fetch i S
                          val (pP,pT) = parsubg "Psi" 1 1 ([],sty)
                          val newSubgTy =
                              foldr
                              (fn (i,_,_,_) => fn S =>
                                  if (#1 i)="iter"
                                  then voonify (~1) i S
                                  else S)
                              (pP,pT) pP
                          val S = swap (i,bv,nam,outrovoo newSubgTy) S
                      in  S
                      end
                      handle missing_voodoo => S
                  end
              val (subgoals,_) =
                  voowrap stuff voolift
                  (fn SS =>
                      foldr (fn (i,_,_,_) => fn S => mangleSubg i S)
                      SS subgoals)
                  voolift (subgoals,VProp)


              (* third we flatten the iters and stick on the
                 shuffPref *)
              val stickTheseBack = shuffPref
              val (back_pxs,back_Phis,back_subgs,back_ys,
                   back_Phind,back_PhiType,back_PhiArgs,back_PhiVis) =
                  choppec (parselim (voo (type_of_constr backElim)))
              fun flitter [] hS _ = ([],hS)
                | flitter ((("iter",_),_,_,_)::planRest)
                          (VBind ((Pi,_),_,ty,subgRest))
                          nextVar =
                  let val depth = voobdep ty
                      val (flatPref,flatTail) =
                          introvool ["flat"] nextVar depth ([],ty)
                      val (pref,tail) = flitter planRest subgRest
                                        (nextVar+depth+1)
                  in  (flatPref@
                       ((("flat",nextVar+depth),(Pi,Vis),"",flatTail)::pref),
                       tail)
                  end
                | flitter (((s,i),bv,nam,_)::planRest) hS nextVar =
                  let val (oneSubgPi,subgRest) = introvool [s] i 1 ([],hS)
                      val ty = #4 (hd oneSubgPi)
                      val (pref,tail) = flitter planRest subgRest nextVar
                  in  (((s,i),bv,nam,ty)::pref,tail)
                  end
              fun flatten ((id,bv,nam,hSubg)::tSubg)
                          ((_,_,_,hSubgPlan)::tSubgPlan) =
                  let val (planPref,_) = parsubg "Phi" 1 1 ([],hSubgPlan)
                  in  (id,bv,nam,
                       outrovoo (stickTheseBack,
                                 outrovoo (flitter planPref hSubg 1)))::
                      (flatten tSubg tSubgPlan)
                  end
                | flatten _ _ = []
              val flattenedSubgs = flatten subgoals back_subgs
(**)
       val _ = vooprintstate (flattenedSubgs,VProp)
(**)
          in  (* story so far *)
              flattenedSubgs
          end 

      fun elimPlan tag args goal =
          let val (er,et) = Require tag
              val ver = voo er
              val peet = parselim (voo et)
              val (pxs,Phis,subgs,ys,Phind,PhiType,PhiArgs,PhiVis) =
                  choppec peet
              val Phisubgs = Phis@subgs
              val PhiArgs = map (fn (Voo v) => v | _ => raise missing_voodoo)
                            PhiArgs   (* just want the ids *)
              val nint = (length pxs)-(length args)
              val _ = if nint<0 then raise RequireFailure else ()
              val s1 = introvool ["w"] 1 nint goal
              val realArgs = args@(mkVl "w" 1 nint)
              val s2 = introvool ["y"] 1 (length ys) s1
              (* tail of s2 is thing to abstract to make Phi *)
              (* realArgs are the args to the elim rule *)
              (* now we must find the voodoo variables corresponding to
                 the xs; if any of the realArgs are VRefs, we must
                 abstract them *)
              fun findxs ((v as ("p",_),_,_,_)::pxt) (ah::at) = 
                  let val (xal,ral,pht) = findxs pxt at
                  in  (xal,ral,voosub v ah pht)
                  end
                | findxs ((u as ("x",n),_,_,_)::pxt) ((ah as Voo v)::at) =
                  let val (xal,ral,pht) = findxs pxt at
                  in  ((n,v)::xal,ral,voosub u ah pht)
                  end
                | findxs ((v as ("x",n),_,_,_)::pxt)
                                  ((ah as VRef b)::at) =
                  let val (xal,ral,pht) = findxs pxt at
                  in  ((n,("abs",n))::xal,(ref_ts b,("abs",n))::ral,
                         voosub v ah pht)
                  end
                | findxs _ _ = ([],[],(Phisubgs,PhiType))
              val (xal,ral,(Phisubgs2,RealPhiType)) = findxs pxs realArgs
              val (_,PhiBody) = refAbstract ral s2
              fun pick ("x",i) = assoc i xal
                | pick v = v
              fun Phintros (h::t) S =
                  let val (s,n) = pick h
                  in  Phintros t (introvool [s] n 1 S)
                  end
                | Phintros _ S = S
              val (PhiPref,_) = Phintros PhiArgs ([],RealPhiType)
              val PhiState = (map vooPiToLda PhiPref,PhiBody)
              val Phi = vooeta (outrovoo PhiState)
              val (RealPhiSubgs,_) =
                  voolift (voorewrite (vooblat ("Phi",Phind) Phi))
                          (Phisubgs2,VProp)
              val theArgs = realArgs@
                            (map (fn (v,_,_,_) => 
                                     if v=("Phi",Phind) then Phi
                                     else Voo v) RealPhiSubgs)
              fun getvis [] _ = []
                | getvis (_::t) ((_,(_,Hid),_,_)::t') = NoShow::(getvis t t')
                | getvis (_::t) ((_,(_,Vis),_,_)::t') = ShowNorm::(getvis t t')
                | getvis _ _ = raise RequireFailure
          in  elide ("Phi",Phind)
              (map vooPiToLda ((#1 s1)@RealPhiSubgs),
               VApp ((ver,theArgs),getvis theArgs (#1 peet)))
          end

      fun appSolve solve j S =
          appSolve solve (j+1) (voosolve ("subgoal",j) (solve j) S)
          handle missing_voodoo => S

      local
      fun doit l r k t =
         (let val ename = "e"^l^r
              val (eq,eqty) = Require ["Eq"]
              val veq = voo eq
              val vequniv = voo ((fn (Bind ((Pi,_),_,u,_)) => u
                                   | _ => raise RequireFailure) (whnf eqty))
              val (eqr,_) = Require ["Eq","refl"]
              val veqr = voo eqr
              val J_goal = outrovoo
              ([(("A",1),(Pi,Hid),"A",vequniv),
                (("x",1),(Pi,Hid),"x",Voo ("A",1)),
                (("y",1),(Pi,Hid),"y",Voo ("A",1)),
                (("exy",1),(Pi,Vis),"exy",
                    VApp ((veq,[Voo ("A",1),Voo ("x",1),Voo ("y",1)]),
                               [NoShow,     ShowNorm,   ShowNorm])),
                (("Phi",1),(Pi,Vis),"Phi",outrovoo
                    ([(("q",1),(Pi,Hid),"q",Voo ("A",1)),
                      ((ename,1),(Pi,Vis),ename,
                          VApp ((veq,[Voo ("A",1),Voo (l,1),Voo (r,1)]),
                                     [NoShow,     ShowNorm,   ShowNorm]))],
                     vequniv)),
                (("H",1),(Pi,Vis),"H",
                   VApp ((Voo ("Phi",1),[Voo (k,1),
                         VApp ((veqr,[Voo ("A",1),Voo (k,1)]),
                                     [NoShow,     ShowNorm])]),
                             [NoShow,ShowNorm]))],
               VApp ((Voo ("Phi",1),[Voo (t,1),Voo ("exy",1)]),
                                    [NoShow,     ShowNorm]))
              (* {A|Type}{x,y|A}{exy:Eq x y}{Phi:{q|A}{exq:Eq x q}Type}
                   (Phi (Eq_refl x))->Phi exy
              *)
              val thePlan = elimPlan ["Eq","elim"] [] ([],J_goal)
              val (subg,_,_,subgType) = fetch ("subgoal",1) thePlan
              val (pref,_) = introvool ["x","Phi","H"] 1 1 ([],subgType)
              val subgProof = outrovoo (map vooPiToLda pref,Voo ("H",1))
              val J_proof = voosolve ("subgoal",1) subgProof thePlan
          in  ((stop J_proof,unvoo J_goal),true)
          end
          handle _ => raise RequireFailure)
      in
      fun eqJDemon ["Eq","J"] = doit "x" "q" "x" "y"
        | eqJDemon ["Eq","J","sym"] = doit "q" "y" "y" "x"
        | eqJDemon _ = raise RequireFailure
      end

      fun depSubstBuild 0 =
         (let (* {B:Type}
                 {b:B}B *)

              val (eq,eqty) = Require ["Eq"]
              val veq = voo eq
              val vequniv = voo ((fn (Bind ((Pi,_),_,u,_)) => u
                                   | _ => raise RequireFailure) (whnf eqty))
              val dep_subst_0_goal_state =
              ([(("B",1),(Pi,Vis),"B",vequniv),
                (("b",1),(Pi,Vis),"b",Voo ("B",1))],
               Voo ("B",1))

              val proof_state =
              ([(("B",1),(Lda,Vis),"B",vequniv),
                (("b",1),(Lda,Vis),"b",Voo ("B",1))],
               Voo ("b",1))

          in  ((stop proof_state,stop dep_subst_0_goal_state),false)
          end
          handle _ => raise RequireFailure)

        | depSubstBuild n =
          if n<1 then raise RequireFailure
          else
         (let val veq = voo (#1 (Require ["Eq"]))
              val oldtag = ["dep","subst",string_of_num (n-1)]
              val (oldref,oldthm) = Require oldtag
              val (oldApref,VBind ((Pi,_),_,AnType,_)) = 
                  introvool ["A","x","y","exy"] 1 (n-1) (start oldthm)
              val (anPref,univ) = introvool ["a"] 1 (n-1) ([],AnType)
              val enoughas = mkVl "a" 1 (n-1)
              val enoughShowNorm = map (fn _ => ShowNorm) enoughas
              val BType = outrovoo (anPref@
                        [(("a",n),(Pi,Vis),"",
                           VApp ((Voo ("A",n),enoughas),enoughShowNorm))],
                                    univ)
              fun substargs i =
                  if i=n then ([Voo ("A",n),Voo ("x",n)],[ShowNorm,ShowNorm])
                  else
                  let val (args,vis) = substargs (i+1)
                  in  ((Voo ("A",i))::(Voo ("x",i))::(Voo ("y",i))::
                        (Voo ("exy",i))::args,
                       NoShow::NoShow::NoShow::ShowNorm::vis)
                  end
              val xnType =
                  VApp ((Voo ("A",n),mkVl "x" 1 (n-1)),enoughShowNorm)
              val ynType =
                  VApp ((Voo ("A",n),mkVl "y" 1 (n-1)),enoughShowNorm)
              val (suba,subv) = substargs 1
              val newthm = outrovoo
                  (oldApref@
                   [(("A",n),(Pi,Hid),"",AnType),
                    (("x",n),(Pi,Hid),"",xnType),
                    (("y",n),(Pi,Hid),"",ynType),
                    (("exy",n),(Pi,Vis),"",
                     VApp ((veq,[ynType,VApp ((voo oldref,suba),subv),
                                                             Voo ("y",n)]),
                                [NoShow,ShowNorm,            ShowNorm])),
                    (("B",1),(Pi,Vis),"B",BType),
                    (("b",1),(Pi,Vis),"b",
                  VApp ((Voo ("B",1),mkVl "x" 1 n),ShowNorm::enoughShowNorm))],
                  VApp ((Voo ("B",1),mkVl "y" 1 n),ShowNorm::enoughShowNorm))

              val outerPlan =
                  introvool ["A","x","y","exy","subgoal"] 1 1
                  ([],outrovoo (elimPlan ["Eq","J"] [] ([],newthm)))
              val (subg,_,_,subgType) = fetch ("subgoal",1) outerPlan

              val mostin = introvool ["A","x","y","exy"] 2 (n-1) ([],subgType)
              val planargs = 
                  map 
                   (fn (("A",j),_,_,_) => VApp ((Voo ("A",j),[Voo ("x",1)]),
                                                             [ShowNorm])
                     | (v,_,_,_) => Voo v) (#1 mostin)
              val allin = introvool ["B","b"] 1 1 mostin

              val plof = elimPlan oldtag planargs allin
              val subgProof = outrovoo
                              (voosolve ("subgoal",1) (Voo ("b",1)) plof)
              val proof = voosolve ("subgoal",1) subgProof outerPlan
          in  ((stop proof,unvoo newthm),true)
          end
          handle _ => raise RequireFailure)

      fun depSubstDemon ["dep","subst",n] =
         (depSubstBuild (atoi n)
          handle _ => raise RequireFailure)
        | depSubstDemon _ = raise RequireFailure

      fun linTriResp lin tri res =
         (let val _ = if lin<0 orelse tri<0 orelse res<1
                      then raise RequireFailure
                      else ()
              val (eq,eqty) = Require ["Eq"]
              val veq = voo eq
              val vequniv = voo ((fn (Bind ((Pi,_),_,u,_)) => u
                                   | _ => raise RequireFailure) (whnf eqty))
              val n = lin+tri
              val linAs = mkVl "A" 1 lin
              val triAs = mkVl "A" (lin+1) n
              val xs = mkVl "x" 1 n
              val ys = mkVl "y" 1 n
              val viss = SNs n;
              val exys = buildLinTriEqs "exy" 1 (linAs,triAs) xs ys
              fun mkUTypes U u lin tri i l p =
                  if i>(lin+tri) then l
                  else if i<=lin
                  then mkUTypes U u lin tri (i+1)
                                (l@[((U,i),(Pi,Hid),"",vequniv)]) p
                  else let val (rs,vs) = ArgsAndVis p ([],[])
                           val newU = [((U,i),(Pi,Hid),"",
                                        outrovoo (p,vequniv))]
                           val newu = [((u,i),(Pi,Vis),"",
                                        flApp ((Voo (U,i),rs),vs))]
                       in  mkUTypes U u lin tri (i+1) (l@newU) (p@newu)
                       end
              val ATypes = mkUTypes "A" "a" lin tri 1 [] []
              fun mkVTypes s v i l p h =
                  if i>n then l
                  else if i<=lin
                  then mkVTypes s v (i+1)
                                (l@[((s,i),(Pi,v),"",Voo ("A",i))]) [] []
                  else let val newV = [((s,i),(Pi,v),"",
                                        flApp ((Voo ("A",i),p),h))]
                       in  mkVTypes s v (i+1) (l@newV) (p@[Voo (s,i)])
                                                       (ShowNorm::h)
                       end
              val xTypes = mkVTypes "x" Hid 1 [] [] []
              val yTypes = mkVTypes "y" Hid 1 [] [] []
              val fPref = mkVTypes "a" Vis 1 [] [] []
              val (aRs,aVs) = ArgsAndVis fPref ([],[])
              val TTypes = mkUTypes "T" "t" 0 res 1 [] []
              fun mkfTypes i l pr pv =
                  if i>res then l
                  else mkfTypes (i+1)
                                (l@[(("f",i),(Pi,Vis),"",
                                     outrovoo (fPref,
                                               flApp ((Voo ("T",i),pr),pv)))])
                                (pr@[VApp ((Voo ("f",i),aRs),aVs)])
                                (ShowNorm::pv)
              val fTypes = mkfTypes 1 [] [] []
              val thePref = splice [ATypes,xTypes,yTypes,exys]
                            (splice [TTypes,fTypes] [])
              (* thePref is the prefix for the goal *)
              fun fix i = flApp ((Voo ("f",i),xs),viss)
              fun fiy i = flApp ((Voo ("f",i),ys),viss)
              val theTail =
                  case res
                    of 1 => VApp ((veq,[Voo ("T",1),fix 1,   fiy 1]),
                                       [NoShow,     ShowNorm,ShowNorm])
                     | _ =>
                  let fun mkRespApp i =
                          let val (iRef,iType) =
                              Require ["lin",string_of_num lin,
                                       "tri",string_of_num tri,
                                       "resp",string_of_num i]
                              val (iPref,_) =
                                  introvool ["T","f"] 1 i
                                 (introvool ["A","x","y","exy"] 1 n
                                            (start iType))
                              val (rs,vs) = ArgsAndVis iPref ([],[])
                              val theApp = VApp ((voo iRef,rs),vs)
                          in  ([Voo ("T",i),fix i,fiy i,theApp],
                               [NoShow,NoShow,NoShow,ShowNorm])
                          end
                      val (subRef,_) =
                          Require ["dep","subst",string_of_num (res-1)]
                      fun mkSubArgs i =
                          if i=res then ([Voo ("T",res),fix res],
                                            [ShowNorm,ShowNorm])
                          else
                          let val (rs,vs) = mkSubArgs (i+1)
                              val (rs',vs') = mkRespApp i
                          in  (rs'@rs,vs'@vs)
                          end
                      val (rs,vs) = mkSubArgs 1
                      val lhs = VApp ((voo subRef,rs),vs)
                      val rhs = fiy res
                      val theType =  VApp ((Voo ("T",res),
                                            mkList fiy 1 (res-1)),
                                           SNs (res-1))
                  in  VApp ((veq,[theType,lhs,rhs]),
                                       [NoShow,ShowNorm,ShowNorm])
                  end
              val theGoal = outrovoo (thePref,theTail)
              val JRef = vooreq ["Eq","J"]
              val (eqr,_) = Require ["Eq","refl"]
              val theProof =
                  case n
                    of 0 =>
                         let val (pref,tail) = introvool ["T","f"] 1 res
                                 ([],theGoal)
                             val rargs = case tail
                                           of VApp ((_,[T,_,x]),_) => [T,x]
                                            | _ => raise RequireFailure
                         in  outrovoo (map vooPiToLda pref,
                                       VApp ((voo eqr,rargs),
                                              [NoShow,ShowNorm]))
                         end
                     | _ =>
                         let val g = introvool ["q"] 1 4
                                     ([],theGoal)
                             val plan = outrovoo
                                        (elimClobber [] JRef g (Voo ("q",4)))
                             val plan =
                                 introvool ["A","x","y","exy","subgoal"] 1 1
                                 ([],plan)
                             val subg = ([],#4 (fetch ("subgoal",1) plan))
                             val (subgPref,_) =
                                 introvool ["T","f"] 1 res                 (
                                 introvool ["A","x","y","exy"] 2 (n-1) subg)
                             val (l',t') = if lin>0 then (lin-1,tri)
                                           else (0,tri-1)
                             val (oldRef,_) =
                                 Require ["lin",string_of_num l',
                                          "tri",string_of_num t',
                                          "resp",string_of_num res]
                             val oldas =
                                 map (fn (("A",i),_,_,_) =>
                                           if lin=0
                                           then VApp ((Voo ("A",i),
                                                       [Voo ("x",1)]),
                                                      [ShowNorm])
                                           else Voo ("A",i)
                                       | (("f",i),_,_,_) =>
                                           VApp ((Voo ("f",i),
                                                  [Voo ("x",1)]),
                                                 [ShowNorm])
                                       | (x,_,_,_) => Voo x)
                                 subgPref
                             val oldvs =
                                 map (fn (_,(_,Hid),_,_) => NoShow
                                       | _ => ShowNorm)
                                 subgPref
                             val subsolve =
                                 outrovoo (map vooPiToLda subgPref,
                                           VApp ((voo oldRef,oldas),oldvs))
                         in  outrovoo (voosolve ("subgoal",1) subsolve plan)
                         end
          in  ((unvoo theProof,unvoo theGoal),true)
          end
          handle _ => raise RequireFailure)

      fun linTriRespDemon ["lin",l,"tri",t,"resp",r] =
         (linTriResp (atoi l) (atoi t) (atoi r)
          handle _ => raise RequireFailure)
        | linTriRespDemon _ = raise RequireFailure

      fun indCasesDemon [iType,"cases"] =
         (let val (iTypeRef,iTypeKind) = Require [iType]
              val (elim,elimType) = Require [iType,"elim"]
              val (acTerm,acType) = fEval (unEval (stop
                                      ([(("P",1),(Lda,Vis),"",VProp),
                                      (("p",1),(Lda,Vis),"",Voo ("P",1))],
                                     Voo ("p",1))))
              val aTerm = voo acTerm
              val aType = voo acType

              val peet = parselim (voo elimType)
              val (params,Phis,subgs,ys,Phind,PhiType,PhiArgs,PhiVis) =
                  choppec peet

              (* to build the cases theorem, we mangle these bits... *)
              (* we throw away the subgoals for the wrong Phi *)
              val (casesSubgs1,drossSubgs) =
                  filter (fn (_,_,_,t) =>
                             (voohead t)=(Voo ("Phi",Phind)))
                         subgs

              (* for each which remains, filter out the Phi premises;
                 note subtle name change too...                         *)
              (* it's also the ideal opportunity to compute some of the
                 proof of the weak subgoals from the strong cases       *)
              val (casesSubgs2,caseProofTails) = ListUtil.unzip
                 (map (fn ((_,i),bv,n,t) =>
                          let val (pref,tail) =
                                  introvool ["q"] 1 (voobdep t) ([],t)
                              val (pref',_) =
                                  filter (fn (_,_,_,c) =>
                                          case (voohead c)
                                            of (Voo ("Phi",_)) => false
                                             | _ => true)
                                         pref
                              val (rs,vs) = ArgsAndVis pref' ([],[])
                          in  ((("con",i),bv,n,outrovoo (pref',tail)),
                               (i,VApp((Voo ("con",i),rs),vs)))
                          end)
                      casesSubgs1)

              (* again we change the name of Phi so it doesn't confuse
                 elimPlan *)
              val casesThm = voorename ("Phi",Phind) ("Psi",1)
                             (params@((fetch ("Phi",Phind) (Phis,VProp))::
                                      casesSubgs2),
                              outrovoo (ys,#2 peet))

              (* now we can prove the theorem *)
              val paramArgs = map (fn x => Voo (#1 x)) params
              val proofPlan = elimPlan [iType,"elim"] paramArgs casesThm

              (* next, we solve the spare Phis by providing a dummy type *)
              fun blatATerm x (VBind ((Pi,v),s,t,r)) =
                              VBind ((Lda,v),s,t,blatATerm x r)
                | blatATerm x _ = x
              val PhisGone =
                  foldr (fn ((_,i),_,_,t) =>
                         if i = Phind then (fn S => S)
                         else voosolve ("Phi",i) (blatATerm aType t))
                        proofPlan
                        Phis

              (* now compute the proofs for the corresponding dross subgoals *)
              (* note that the trick depends crucially on calling the args
                 q1... like we did when we computed the tails                *)
              fun solve j =
                  let val (_,_,_,t) = fetch ("subgoal",j) PhisGone
                      val (pref,tail) =
                          introvool ["q"] 1 (voobdep t) ([],t)
                  in  outrovoo (map vooPiToLda pref,
                                assoc j caseProofTails
                                handle Assoc => aTerm)
                  end 
              val proofState = appSolve solve 1 PhisGone
 
          in  ((stop proofState,stop casesThm),true)
          end
          handle _ => raise RequireFailure)
        | indCasesDemon _ = raise RequireFailure

      fun indInversionDemon [iType,"inversion"] =
         (let val (casesRef,casesType) = Require [iType,"cases"]
              val pect = parselim (voo casesType)
              val (params,Phis,subgs,ys,Phind,PhiType,PhiArgs,PhiVis) =
                  choppec pect
              (* take the universe from what cases eliminates over *)
              val invUniv = voohead PhiType

              val paramsysXi = params@ys@[(("Phi",1),(Pi,Hid),"",invUniv)]
              val prefLen = length paramsysXi
              val (invFrontEnd,invBackEnd) =
                  introvool ["Xi"] 1 prefLen
                  ([],outrovoo (paramsysXi,Voo ("Phi",1)))
              val target = Voo ("Xi",prefLen-1)

              (* inversion is just Clobber with cases, right? *)

              val (_,_,RealSubgs,_,solution) =
                  elimClobberPlan false invFrontEnd (voo casesRef)
                                  ([],invBackEnd)
                                  target

              val invPrefix = invFrontEnd@RealSubgs
              val theTheorem = outrovoo (invPrefix,invBackEnd)
              val theProof = vooeta (outrovoo (map vooPiToLda invPrefix,
                                               solution))
          in  ((unvoo theProof,unvoo theTheorem),true)
          end
          handle _ => raise RequireFailure)
        | indInversionDemon _ = raise RequireFailure

      fun switchNames s t (Voo (n,i)) = if n=s then Voo (t,i)
                                        else raise voodoo_no_rewrite
        | switchNames _ _ _ = raise voodoo_no_rewrite

      fun switchCtxt s t [] = []
        | switchCtxt s t ((h as ((n,i),b,q,ty))::rest) =
          ((if n=s then t else n,i),b,q,voorewrite (switchNames s t) ty)::
          (switchCtxt s t rest)

      fun analyseInd iType =
         (let val (eq,eqty) = Require ["Eq"]
              val veq = voo eq
              val vequniv = voo ((fn (Bind ((Pi,_),_,u,_)) => u
                                   | _ => raise RequireFailure) (whnf eqty))
              val (casesRef,casesThm) = Require [iType,"cases"]
              val (casesPref,_) = parselim (voo casesThm)
              fun getParams ((("Phi",_),_,_,_)::_) = []
                | getParams ((("x",_),_,_,_)::_) =
                  raise RequireFailure
                | getParams ((h as (("p",_),_,_,_))::t) = h::(getParams t)
                | getParams _ = raise RequireFailure
              fun getYs [] = []
                | getYs ((("y",i),v,_,u)::t) =
                  (("y",i),v,"",u)::(getYs t)
                | getYs (h::t) = getYs t
              val params = getParams casesPref
              val paramsAsArgs = map (fn x => (Voo (#1 x))) params
              val ys = getYs casesPref
              val xs = switchCtxt "y" "x" ys
              val triangY = triangularise [] ys
              val k_value = length triangY
              val kxs = mkVl "x" 1 k_value
              val exys = build_equations "exy" 1 triangY kxs
                                                      (mkVl "y" 1 k_value)
              val es = switchCtxt "exy" "e" exys
              val PhiType = outrovoo (es,vequniv)
              
          in  { veq                 = veq,
                vequniv             = vequniv,
                casesRef            = casesRef,
                params              = params,
                paramsAsArgs        = paramsAsArgs,
                ys                  = ys,
                xs                  = xs,
                triangY             = triangY,
                k_value             = k_value,
                kxs                 = kxs,
                exys                = exys,
                es                  = es,
                PhiType             = PhiType
              }
          end
          handle _ => raise RequireFailure)

      fun indNoConfStmtDemon [iType,"no","confusion","statement"] =
         (let val 
              { veq                 = veq,
                vequniv             = vequniv,
                casesRef            = casesRef,
                params              = params,
                paramsAsArgs        = paramsAsArgs,
                ys                  = ys,
                xs                  = xs,
                triangY             = triangY,
                k_value             = k_value,
                kxs                 = kxs,
                exys                = exys,
                es                  = es,
                PhiType             = PhiType
              } = analyseInd iType

              val goalState = (params,outrovoo (xs@ys@exys@
                               [(("Phi",1),(Pi,Vis),"Phi",PhiType)],
                               vequniv))

              val planX = elimPlan [iType,"cases"] paramsAsArgs goalState
(*
      val _ = vooprintstate planX
*)
              (* now solve the subgoals corresponding to the constructors *)
              (* by introducing the arguments and doing cases on y...     *)

              fun solveSubX i =
                  let val (_,_,_,subg) = fetch ("subgoal",i) planX
                      val subDep = voobdep subg
                      val (theBs,yGoal) =
                          introvool ["b"] 1 (subDep-k_value-k_value-1)
                          ([],subg)       (* conargs, ys,   exys,  Phi *)
                      val planY = vooglue (map vooPiToLdaElideName theBs)
                                  (elimPlan [iType,"cases"] paramsAsArgs 
                                  ([],yGoal))

                      (* now solve the subgoals corresponding to y's cons *)
                      (* off-diags just go [..]{T|Type}T                  *)
                      (* diags become injectivity thms                    *)

                      fun solveSubY j =
                          let val (_,_,_,subg) = fetch ("subgoal",j) planY
                              val subDep = voobdep subg
                              val (theCs,rest) = (* theCs are con args *)
                                  introvool ["c"] 1 (subDep-k_value-1)
                                  ([],subg)               (* exys, Phi *)
                              val (theExys,rest2) =
                                  introvool ["exy"] 1 k_value ([],rest)
                              val (thePhi,_) = (* tail should be Type etc *)
                                  introvool ["Phi"] 1 1 ([],rest2)
                              val thePref = theCs@(theExys@thePhi)
                              val theLdas = map vooPiToLdaElideName thePref
                          in  if i<>j  (* off diag *)
                                 then outrovoo (theLdas,
                                       VBind ((Pi,Vis),"KILL",vequniv,VRel 1))
                              else (* inject right here *)
                              let val linTriC = linearTriangular theCs
                                  val lin = length (#1 linTriC)
                                  val tri = length (#2 linTriC)
                                  val n_value = lin+tri
                                  val ebcs = buildLinTriEqs "ebc" 1 linTriC
                                                    (mkVl "b" 1 n_value)
                                                    (mkVl "c" 1 n_value)
                                  (**)
                                  fun respArgs _ [] = []
                                    | respArgs i (hA::tA) =
                                      hA::(Voo ("b",i))::(Voo ("c",i))::
                                      (Voo ("ebc",i))::(respArgs (i+1) tA)
                                  val respAsFront = respArgs 1 (*triangC*)
                                                    ((#1 linTriC)@
                                                     (#2 linTriC))
                                  val respVsFront =
                                      map (fn Voo ("ebc",_) => ShowNorm
                                            | _ => NoShow) respAsFront
                                  val ldaCs = map vooPiToLdaElideName theCs
                                  fun mkTfs ((("exy",i),_,_,
                                             VApp ((_,[T,_,tail]),_))::rest)
                                            (hY::tY) =
                                      (i,[hY,vooeta (outrovoo (ldaCs,tail))])
                                      ::(mkTfs rest tY)
                                    | mkTfs [] [] = []
                                    | mkTfs _ _ = ((print "Ulp!");
                                                raise RequireFailure)
                                  val TfAList = mkTfs theExys triangY
                                  fun respAsBack 0 l = l
                                    | respAsBack i l =
                                      respAsBack (i-1) ((assoc i TfAList)@l)
                                  fun respVsBack 0 = []
                                    | respVsBack i = NoShow::ShowNorm::
                                                     (respVsBack (i-1))
                                  fun resp i =
                                      let val (respRef,_) =
                                          Require ["lin",string_of_num lin,
                                                   "tri",string_of_num tri,
                                                   "resp",string_of_num i]
                                          (**)
                                      in  VApp ((voo respRef,
                                             respAsFront@(respAsBack i [])),
                                             respVsFront@(respVsBack i))
                                      end
                                  val kSNs = SNs k_value
                                  val theHyp = outrovoo (ebcs,
                                                 VApp ((Voo ("Phi",1),
                                                       mkList resp 1 k_value),
                                                      kSNs))
                                  val theTail = VApp ((Voo ("Phi",1),
                                                       mkVl "exy" 1 k_value),
                                                      kSNs)
                                  val proofState = (theLdas@
                                       [(("Hyp",1),(Pi,Vis),"",theHyp)],
                                                    theTail)
(*
   val _ = vooprintstate proofState
*)
                              in  outrovoo proofState
                              end
                          end
                  in  outrovoo (appSolve solveSubY 1 planY)
                  end
              val proofState = appSolve solveSubX 1 planX
(*
   val _ = vooprintstate proofState
*)
          in  ((stop proofState,stop goalState),true)
          end
          handle _ => raise RequireFailure)
        | indNoConfStmtDemon _ = raise RequireFailure

      fun indDepNoConfDemon [iType,"dep","no","confusion"] =
         (let val (eqr,_) = Require ["Eq","refl"]
              val veqr = voo eqr
              val (stmtRef,stmtThm) =
                  Require [iType,"no","confusion","statement"]

              val theStmt = (fn (Ref b) => voo (ref_VAL b)
                              | _ => raise RequireFailure) stmtRef

              val 
              { veq                 = veq,
                vequniv             = vequniv,
                casesRef            = casesRef,
                params              = params,
                paramsAsArgs        = paramsAsArgs,
                ys                  = ys,
                xs                  = xs,
                triangY             = triangY,
                k_value             = k_value,
                kxs                 = kxs,
                exys                = exys,
                es                  = es,
                PhiType             = PhiType
              } = analyseInd iType

              fun mangleVis (("exy",i),(b,_),s,t) = (("exy",i),(b,Vis),s,t)
                | mangleVis (("Phi",i),(b,_),s,t) = (("Phi",i),(b,Vis),s,t)
                | mangleVis (v,(b,_),s,t) = (v,(b,Hid),s,t)
              val noParamGoalPref = map mangleVis
                            (splice [xs,ys,exys]
                             [(("Phi",1),(Pi,Vis),"",PhiType)])
              val (args,vis) = ArgsAndVis params             (
                               ArgsAndVis xs                (
                               ArgsAndVis ys               (
                               ArgsAndVis exys            (
                               [Voo ("Phi",1)],[ShowNorm] ))))
              val paramHid = map mangleVis params
              val goalTail = VApp ((voo stmtRef,args),vis)
              val goalState = (paramHid@noParamGoalPref,goalTail)
(*
    val _ = vooprintstate goalState
*)
              val introParams = (paramHid,outrovoo (noParamGoalPref,goalTail))

              (* here we chop up the statement to get the bits we need *)

              val (_,casesCases) = introvool ["p"] 1 (voobdep theStmt)
                                   ([],theStmt)
              val addOn = (length params)+1
              fun solveCase i =
                  let val caseX = vapparg (addOn+i) casesCases
                      val nConArgs = voobdep caseX
                      val (_,nextApp) = introvool ["b"] 1 nConArgs ([],caseX)
                      val caseY = vapparg (addOn+i) nextApp
                      val (bPref,bTail) = introvool ["b"] 1 nConArgs ([],caseY)
                      val (_,eTail) = introvool ["exy"] 1 k_value ([],bTail)
                      val (oldPref,_) = introvool ["Phi","Hyp"] 1 1
                                        (bPref,eTail)
                      fun mkRefl (i,_,_,t) =
                          VApp ((veqr,[t,Voo i]),[NoShow,ShowNorm])
                      val theTail = VApp ((Voo ("Hyp",1),map mkRefl bPref),
                                          map (fn _ => ShowNorm) bPref)
                  in  outrovoo (map vooPiToLdaElideName oldPref,theTail)
                  end
                  (* note that this should raise missing_voodoo when *)
                  (* i is one too many, since vapparg will           *)
              
              fun proveTheTheorem j subgS =
                  if j>k_value
                      then
                      let val planCases = elimPlan [iType,"cases"] 
                                          paramsAsArgs ([],outrovoo
                                          (vooglue xs subgS))
                          val (_,tail) = appSolve solveCase 1 planCases
                          val (rs,vs) = ArgsAndVis xs ([],[])
                      in  VApp ((tail,rs),vs)
                      end
                  else
                  let val intro3 = introvool ["x","y","exy"] j 1 subgS
                      val (_,_,_,xt) = fetch ("x",j) intro3
                      val planJ = elimPlan ["Eq","J"]
                                  [xt,Voo ("x",j),Voo ("y",j),Voo ("exy",j)]
                                  intro3
                      val (_,_,_,newSubG) = fetch ("subgoal",1) planJ
                      val subProof = proveTheTheorem (j+1) ([],newSubG)
                      val proof = outrovoo                          (
                                  elide ("subgoal",1)              (
                                  voosub ("subgoal",1) subProof planJ ))
                  in  proof
                  end

              val wholeProof = proveTheTheorem 1 introParams

          in  ((unvoo wholeProof,stop goalState),true)
          end
          handle _ => raise RequireFailure)
        | indDepNoConfDemon _ = raise RequireFailure

      fun KMangleBuild n =
          if n<2 then raise RequireFailure
          else
         (let val (eq,eqty) = Require ["Eq"]
              val veq = voo eq
              val vequniv = voo ((fn (Bind ((Pi,_),_,u,_)) => u
                                   | _ => raise RequireFailure) (whnf eqty))
              val nType = VApp ((Voo ("A",n),mkVl "x" 1 (n-1)),SNs (n-1))
              fun makebits (bits as (As,xs)) i =
                  if i>n then (As,xs)
                  else
                  makebits (As@[(("A",i),(Pi,Hid),"",
                                outrovoo (xs "a" Vis,vequniv))],
                            fn s => fn v =>
                            (xs s v)@[((s,i),(Pi,v),"",
                                       VApp ((Voo ("A",i),mkVl s 1 (i-1)),
                                                          SNs (i-1)))])
                           (i+1)
              val (As,xfun) = makebits ([],fn s => fn v => []) 1
              val xs = xfun "x" Hid
              fun makeEs 1 _ _ = (("e",1),(Pi,Vis),"",
                            VApp ((veq,[Voo ("A",1),Voo ("x",1),Voo ("x",1)]),
                                        [NoShow,     ShowNorm,   ShowNorm]))::
                            (makeEs 2 [Voo ("A",1),Voo ("x",1),Voo ("x",1),
                                       Voo ("e",1)]
                        [NoShow,NoShow,NoShow,ShowNorm,ShowNorm,ShowNorm] )
                | makeEs i rs vs =
                  let val (subRef,_) = Require ["dep","subst",
                                                string_of_num (i-1)]
                      val lhs = VApp ((voo subRef,
                                      rs@[Voo ("A",i),Voo ("x",i)]),vs)
                  in  if i=n then [(("e",n),(Pi,Vis),"",
                                    VApp ((veq,[nType,
                                                lhs,Voo ("y",n)]),
                                          [NoShow,ShowNorm,ShowNorm]))]
                      else (("e",i),(Pi,Vis),"",
                            VApp ((veq,[VApp ((Voo ("A",i),
                                              mkVl "x" 1 (i-1)),
                                              SNs (i-1)),
                                        lhs,Voo ("x",i)]),
                                  [NoShow,ShowNorm,ShowNorm]))::
                           (makeEs (i+1) (rs@[Voo ("A",i),Voo ("x",i),
                                              Voo ("x",i),Voo ("e",i)])
                            (NoShow::NoShow::NoShow::ShowNorm::vs))
                  end
              val es = makeEs 1 [] []
              val moreCtxt = [(("y",n),(Pi,Hid),"",nType),
                              (("Psi",1),(Pi,Vis),"",
                               VBind ((Pi,Vis),"e",
                                      VApp ((veq,[nType,Voo ("x",n),
                                                  Voo ("y",n)]),
                                          [NoShow,ShowNorm,ShowNorm]),
                                      vequniv))]
              val goalState = (As@xs@moreCtxt@es,vequniv)

              val introAPsi = introvool ["Psi"] 1 1    (
                              introvool ["y"] n 1     (
                              introvool ["x"] 1 n    (
                              introvool ["A"] 1 n   (
                              [],outrovoo goalState ))))

              fun proveThm i subg =
                  if i=n then Voo ("Psi",1)
                  else
                  let val (_,_,_,xty) = fetch ("x",i) introAPsi
                      val introE = introvool ["e"] i 1 subg
                      val planK = elimPlan ["Eq","K"]
                                           [xty,Voo ("x",i),Voo ("e",i)]
                                           introE
                      val (_,_,_,newSubg) = fetch ("subgoal",1) planK
                  in  outrovoo                                              (
                      elide ("subgoal",1)                                  (
                      voosub ("subgoal",1)
                                        (proveThm (i+1) ([],newSubg)) planK))
                  end

              val proofTerm = proveThm 1 introAPsi
                                                       
          in  ((unvoo proofTerm,stop goalState),true)
          end
          handle _ => raise RequireFailure)
        | KMangleBuild _ = raise RequireFailure

      fun KMangleDemon ["K","mangle",n] =
         (KMangleBuild (atoi n)
          handle _ => raise RequireFailure)
        | KMangleDemon _ = raise RequireFailure

      fun indNoConfDemon [iType,"no","confusion"] =
         (let val (eqr,_) = Require ["Eq","refl"]
              val veqr = voo eqr
              val 
              { veq                 = veq,
                vequniv             = vequniv,
                casesRef            = casesRef,
                params              = params,
                paramsAsArgs        = paramsAsArgs,
                ys                  = ys,
                xs                  = xs,
                triangY             = triangY,
                k_value             = k_value,
                kxs                 = kxs,
                exys                = exys,
                es                  = es,
                PhiType             = PhiType
              } = analyseInd iType
              val (johnnyRef,johnnyType) =
                  Require [iType,"dep","no","confusion"]
          in  if k_value=1 then ((johnnyRef,johnnyType),true)
              else
              let val (_,_,_,ykType) = fetch ("x",k_value) (xs,VProp)
                  val exykType = VApp ((veq,[ykType,Voo ("x",k_value),
                                                    Voo ("y",k_value)]),
                                            [NoShow,ShowNorm,ShowNorm])
                  val PsiType = outrovoo ([(("e",k_value),(Pi,Vis),"",
                                            exykType)],vequniv)
                  val ldaPref = (map vooPiToLdaHide (params@xs))@
                                [(("y",k_value),(Lda,Hid),"",ykType),
                                 (("exy",k_value),(Lda,Vis),"",exykType),
                                 (("Psi",1),(Lda,Vis),"",PsiType)]
                  val (KMangRef,_) = Require ["K","mangle",
                                              string_of_num k_value]
                  val mangArgs = triangY@(mkVl "x" 1 k_value)@
                                         [Voo ("y",k_value),Voo ("Psi",1)]
                  val mangVis = (tl (map (fn _ => NoShow) mangArgs))@[ShowNorm]
                  val Phi = VApp ((voo KMangRef,mangArgs),mangVis)
                  fun mkJohnny 0 =
                      let val (rs,vs) = mkJohnny 1
                      in  (paramsAsArgs@rs,
                           (map (fn _ => NoShow) paramsAsArgs)@vs)
                      end
                    | mkJohnny i =
                      if i<k_value then
                          let val (rs,vs) = mkJohnny (i+1)
                              val (_,_,_,xiType) = fetch ("x",i) (xs,VProp)
                          in  ((Voo ("x",i))::(Voo ("x",i))::
                               (VApp ((veqr,[xiType,Voo ("x",i)]),
                                            [NoShow,ShowNorm]))::rs,
                               NoShow::NoShow::ShowNorm::vs)
                          end
                      else ([Voo ("x",k_value),Voo ("y",k_value),
                             Voo ("exy",k_value),Phi],
                            [NoShow,NoShow,ShowNorm,ShowNorm])
                  val (rs,vs) = mkJohnny 0
                  val theTail = VApp ((voo johnnyRef,rs),vs)
                  val theProof = stop (ldaPref,theTail)
              in  ((theProof,type_of_constr theProof),true)
              end
          end
          handle _ => raise RequireFailure)
        | indNoConfDemon _ = raise RequireFailure

      fun KJunify n =
          let val (_,goal) = goaln (~9999)
              val bof = ([(("goal",1),(Lda,Vis),"",voo goal)],Voo ("goal",1))
              val thePlan = voonify n ("goal",1) bof
              val plan_c = unEval (stop thePlan)
          in  Refine (~9999) 0 plan_c
          end

      val cleverClobberFlag = ref true

      fun findPrem c i goal =
          let exception shesNotThere
              val s = case c
                        of Ref_c s => s
                         | _ => ""
              fun get_name n (Bind ((Pi,_),s',_,r)) =
                  if s=s' then n
                  else get_name (n+1) r
                | get_name _ _ = raise shesNotThere (* how would I know? *)
              fun get_num k m (Bind ((Pi,_),w,_,r)) =
	          if (var_occur r) then get_num (k+1) m r
	          else if m=i then k
		       else get_num (k+1) (m+1) r
	        | get_num _ _ _ = failwith
                                  "there aren't that many (..)-> premises"
              val vgoal = start goal
          in  let val howMany = (case i
                                   of 0 => get_name 1
                                    | i => get_num 1 1)   goal
              in  (introvool ["q"] 1 howMany (start goal),Voo ("q",howMany))
              end
              handle shesNotThere => (vgoal,voo (#1 (fEval c)))
          end

      fun DedicatedTac c i tagTail =
          let val _ = if (activeProofState()) then ()
                      else failwith "Not in active proof state"
              val goal = #2 (goaln (~9999))
              val (vgoal,target) = findPrem c i goal
              val eTypeName =
                  case #1 (vooparseapp
                       (voowrap (#1 vgoal)
                        construe (whnf o type_of_constr) review target))
                    of VRef b => ref_nam b
                     | _ => failwith "Couldn't find type"
              val rule = vooreq (eTypeName::tagTail)
              val eric = if !cleverClobberFlag then elimClobberClever
                                               else elimClobberGen
          in  tactic_wrapper
              (fn () => applyPlan (eric [] rule vgoal target))
              ()
          end

  in

      type cnstr_c = cnstr_c

      exception noQnify = noQnify

      fun KJunifyTac n = tactic_wrapper (fn () => KJunify n) ()

      val cleverClobberFlag = cleverClobberFlag

      fun ClobberTac c i rule =
          let val _ = if (activeProofState()) then ()
                      else failwith "Not in active proof state"
              val goal = #2 (goaln (~9999))
              val (vgoal,target) = findPrem c i goal
              val rule = (#1 (fEval rule))
              val eric = if !cleverClobberFlag then elimClobberClever
                                               else elimClobberGen
          in  tactic_wrapper
              (fn () => applyPlan
                       (eric [] (voo rule) vgoal target))
              ()
          end

      fun ElimTac c i = DedicatedTac c i ["elim"]
      fun InvertTac c i = DedicatedTac c i ["inversion"]

      fun InitialiseQnify () =
          ( (*
            (requireDemons := []);
            *)
            (AddRequireDemon eqJDemon);
            (AddRequireDemon depSubstDemon);
            (AddRequireDemon linTriRespDemon);
            (AddRequireDemon indCasesDemon);
            (AddRequireDemon indInversionDemon);
            (AddRequireDemon indNoConfStmtDemon);
            (AddRequireDemon indDepNoConfDemon);
            (AddRequireDemon KMangleDemon);
            (AddRequireDemon indNoConfDemon);
            ()
          )
  end
end

functor ConorQnifyNeeds ( structure ConorRequire : CONORREQUIRE
(*                          structure Voodoo       : VOODOO*)
                          structure Namespace    : NAMESPACE
                          structure Synt         : SYNT
                          structure Toplevel     : TOPLEVEL
                          structure Concrete     : CONCRETE
    sharing type Synt.cnstr_c =     Concrete.cnstr_c
        and type Toplevel.cnstr_c = Concrete.cnstr_c
                        ) : CONORQNIFYNEEDS =
struct
  local
    open StringCvt
  in
    structure Voodoo = Voodoo
    structure ConorRequire = ConorRequire
    structure Namespace = Namespace
    structure Synt = Synt
    structure Toplevel = Toplevel
    structure Concrete = Concrete
    val atoi = atoi
    val sameTerm = sameTerm
    val weakHeadRed = whnf
  end
end

(*
structure ConorQnifyNeeds = ConorQnifyNeeds (
        structure ConorRequire = ConorRequire
(*        structure Voodoo = Voodoo *)
        structure Namespace = Namespace
        structure Synt = Synt
        structure Toplevel = Toplevel
        structure Concrete = Concrete )

structure ConorQnify = ConorQnify (
        structure ConorQnifyNeeds = ConorQnifyNeeds)
*)(*
open ConorQnify
*)

