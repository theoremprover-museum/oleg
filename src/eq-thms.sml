(* Require demons for substitution operators and respect theorems *)

fun vooDemon ["Voo",s,I] =
   (let val i = atoi I
        val thing = vid (getNamespace(),Prop) (s,i)
    in  (thing,type_of_constr thing)
    end
    handle _ => raise RequireFailure)
  | vooDemon _ = raise RequireFailure

fun vooEqJDemon (tag as "Eq"::"J"::what) =
   (let val J = on (start (?
                    (case what
                       of [] =>      "{A|Type}{x,y|A}{exy:%Eq% x y}"^
                                     "{Phi:{q|A}(%Eq% x q)->Type}"^
                                       "(Phi (%Eq refl% x))->"^
                                       "Phi exy"
                        | ["sym"] => "{A|Type}{x,y|A}{exy:%Eq% x y}"^
                                     "{Phi:{q|A}(%Eq% q y)->Type}"^
                                       "(Phi (%Eq refl% y))->"^
                                       "Phi exy"
                        | _ => raise RequireFailure)))
                [introvool ["A","x","y","exy","Phi","phirefl"] 1 1,
                 vooGoal [("type",1),("J",1),("reds",1)] ("goal",1),
                 Elim MaximalStrat (?"%Eq elim%")
                      [("goal",1),("exy",1),("reds",1)],
                 vooattack ("subgoal",1) ("refl",1),
                 vooIntroTac ("refl",1),
                 vooRefineId ("refl",1) "" ("phirefl",1),
                 vookcatta ("subgoal",1)]
    in  vooQED [("type",1),("J",1),("reds",1)] tag J
    end
    handle _ => raise RequireFailure)
  | vooEqJDemon _ = raise RequireFailure

fun vooEqSymDemon ["Eq","sym"] =
   (let val SYM = on (start (?"{T|Type}{x,y|T}(%Eq% x y)->%Eq% y x"))
                  [introvool ["T","x","y","e"] 1 1,
                   vooGoal [("type",1),("sym",1),("reds",1)] ("goal",1),
                   Elim MaximalStrat (Req ["Eq","J"])
                        [("goal",1),("e",1),("reds",1)],
                   vooattack ("subgoal",1) ("refl",1),
                   vooIntroTac ("refl",1),
                   vooRefineTac ("refl",1) "" (?"%Eq refl%"),
                   vookcatta ("subgoal",1)]
    in  vooQED [("type",1),("sym",1),("reds",1)] ["Eq","sym"] SYM
    end
    handle _ => raise RequireFailure)
  | vooEqSymDemon _ = raise RequireFailure

fun vooDepSubstDemon (tag as ["dep","subst",N]) =
  ((case atoi N
      of 0 => let val ds0 = on (start (?"{B|Type}{b:B}B"))
                              [introvool ["B","b"] 1 1,
                               vooGoal [("type",1),("ds",0)] ("goal",1),
                               vooRefineTac ("goal",1) ""
                                  (?"[B|Type][b:B]b")]
              in  vooQED [("type",1),("ds",0)] tag ds0
              end
       | n => let val _ = if n<1 then raise RequireFailure else ()
                  val m = n-1
                  val (oldPf,oldThm) = Require ["dep","subst",string_of_num m]
                  val (oldP,oldT) = intromangvool anon ["A","x","y","exy"] 1 m
                                    (start oldThm)
                  val (aa,vv) = ArgsAndVis iota oldP
                  val (oldP,oldT) = voomangin (hide o anon) ("A",n) (oldP,oldT)
                  val (xT,yT) = case oldT
                                  of Bind (_,_,xT,yT) => (xT,yT)
                                   | _ => raise RequireFailure
                  val S1 = on (oldP,Prop) [voofloat (("x",n),(Pi,Hid),"",xT),
                                           voofloat (("y",n),(Pi,Hid),"",yT)]
                  val aa = aa@[vid S1 ("A",n),vid S1 ("x",n)]
                  val vv = vv@[ShowNorm,ShowNorm]
                  val yN = vid S1 ("y",n)
                  val S2 = voofloat (("exy",n),(Pi,Vis),"",
                                     App ((Req ["Eq"],[type_of_constr yN,
                                           whnf (App ((oldPf,aa),vv)),yN]),
                                          [NoShow,ShowNorm,ShowNorm])) S1
                  val (justXs,_) = voofilter (isItA"x") (#1 S2)
                  val (BPref,_) = copyCtxt ((vNam "a") o vise) justXs
                  val Bref = noo ((Pi,Vis),"B") ("B",1) (BPref,?"Type")
                  val S3 = ((cons Bref)**iota) S2
                  val B = Ref Bref
                  fun bT s = MkApp ((B,mkList (fn i => vid S3 (s,i)) 1 n),
                                       mkList (fn i => ShowNorm) 1 n)
                  val theType = vooin ("b",1)
                                (#1 S3,Bind ((Pi,Vis),"",bT "x",bT"y"))

                  (* Got the type; now do the proof; *)

                  val dsn = on theType
                        [vooGoal [("type",1),("ds",n),("reds",1)] ("goal",1),
                         Elim MaximalStrat (Req ["Eq","J"])
                         [("goal",1),("exy",1),("reds",1)]]
                  val dsn = on dsn
                           (if n=1
                            then [vooattack ("subgoal",1) ("refl",1),
                                  vooIntroTac ("refl",1),
                                  vooRefineId ("refl",1) "" ("b",1),
                                  vookcatta ("subgoal",1)]
                            else [Elim MinimalStrat oldPf
                                  [("subgoal",1),("exy",n)],
                                  vooattack ("subgoal",1) ("refl",1),
                                  vooIntroTac ("refl",1),
                                  vooRefineId ("refl",1) "" ("b",1),
                                  vookcatta ("subgoal",1)])

              in  vooQED [("type",1),("ds",n),("reds",1)] tag dsn
              end)
    handle _ => raise RequireFailure)
  | vooDepSubstDemon _ = raise RequireFailure

fun triang ctxt = vooctxtrec
    {hitBot = fn _ => ([],[],[]), hitDom = voocontinue,
     hitVoo = fn (id,D) => fn b => fn _ => fn rect =>
              let val (tris,ldas,zap) = rect ()
                  val tri = $! (vooetastate (ldas,zap%>>(ref_typ b)))
                  val b' = ldify (alBind zap ((ref_bd b):!
                                              (Voo (id,vooCopy D))))
              in  (tris@[tri],b'::ldas,(b,Ref b')::zap)
              end} ctxt

fun triEqs name ind AA ll rr soFar =
    let val Eq = Req ["Eq"]
        fun te2 ind dep sArg sVis aArg aVis [] [] [] soFar = soFar
          | te2 ind dep sArg sVis aArg aVis
                (Ah::At) (lh::lt) (rh::rt) soFar =
            let val eqty = MkApp ((Ah,aArg),aVis) (* or could infer this *)
                val dslh = if dep=0 then lh else
                           MkApp ((Req ["dep","subst",string_of_num dep],
                                   sArg@[Ah,lh]),sVis)
                val theq = MkApp ((Eq, [eqty,   dslh,     rh]),
                                      [NoShow,ShowNorm,ShowNorm])
                val b = noo ((Pi,Vis),"") (name,ind) ([],theq)
                val sArg = sArg@[Ah,lh,rh,Ref b]
                val sVis = NoShow::NoShow::NoShow::ShowNorm::sVis
                val aArg = aArg@[rh]
                val aVis = ShowNorm::aVis
            in  te2 (ind+1) (dep+1) sArg sVis aArg aVis
                    At lt rt (b::soFar)
            end
          | te2 _ _ _ _ _ _ _ _ _ _ = raise RequireFailure
    in  te2 ind 0 [] [ShowNorm,ShowNorm] [] [] AA ll rr soFar
    end

fun linearTriangular ctxt = vooctxtrec
    {hitBot = fn _ => fn C => ([],[]),
     hitDom = fn _ => fn _ => fn _ => fn rect => fn C => rect () C,
     hitVoo = fn _ => fn b => fn _ => fn rect => fn C =>
              let val C' = C@[b]
                  val (lins,tris) = rect () C'
              in  if tris=[] (* not tried yet *)
                  then if exists (voobinb b) C (* need to triangle *)
                       then (lins,#1 (triang C'))
                       else (lins@[ref_typ b],[])
                  else (lins,tris)
              end} ctxt []

fun buildLinTriEqs name ind (lins,tris) ll rr =
    let val Eq = Req ["Eq"]
        fun blte ind [] ll rr soFar = triEqs name ind tris ll rr soFar
          | blte ind (Ah::At) (lh::lt) (rh::rt) soFar =
            let val theq = MkApp ((Eq,[Ah,lh,rh]),[NoShow,ShowNorm,ShowNorm])
                val b = noo ((Pi,Vis),"") (name,ind) ([],theq)
            in  blte (ind+1) At lt rt (b::soFar)
            end
          | blte _ _ _ _ _ = raise RequireFailure
    in  blte ind lins ll rr []
    end


fun vooLinTriRespDemon (tag as ["lin",L,"tri",T,"resp",R]) =
   (let val lin = atoi L
        val tri = atoi T
        val res = atoi R
        val _ = if lin<0 orelse tri<0 orelse res<1
                then raise RequireFailure
                else ()
        val Eq = Req ["Eq"]
        val Univ = ?"Type"
        fun mkUBinds U u lin tri =
            let val tot = lin+tri
                fun mkUB ind l p =
                    if ind>tot then l
                    else if ind<=lin
                    then mkUB (ind+1)
                         ((noo ((Pi,Hid),"") (U,ind) ([],Univ))::l) []
                    else let val (aa,vv) = ArgsAndVis iota p
                             val newU = noo ((Pi,Hid),"") (U,ind)
                                            ([],$!(p,Univ))
                             val newu = noo ((Pi,Vis),"") (u,ind)
                                            ([],MkApp ((Ref newU,aa),vv))
                         in mkUB (ind+1) (newU::l) (newu::p)
                         end
            in  mkUB
            end
        val tot = lin+tri
        val ABinds = mkUBinds "A" "a" lin tri 1 [] []
        fun $i = vid (ABinds,Prop) ("A",i)
        fun mkVBinds s v =
            let fun mkVB i l (aa,vv) = if i>tot then l
                    else
                    let val newV = noo ((Pi,v),"") (s,i)
                                       ([],MkApp (($i,aa),vv))
                    in  mkVB (i+1) (newV::l)
                        (if i<=lin then ([],[])
                         else (aa@[Ref newV],ShowNorm::vv))
                    end
            in  mkVB
            end
        val xBinds = mkVBinds "x" Hid 1 [] ([],[])
        val yBinds = mkVBinds "y" Hid 1 [] ([],[])
        val fPref = mkVBinds "a" Vis 1 [] ([],[])
        val (faa,fvv) = ArgsAndVis iota fPref
        val linAs = mkList (fn i => vid (ABinds,Prop) ("A",i)) 1 lin
        val triAs = mkList (fn i => vid (ABinds,Prop) ("A",i)) (lin+1) tot
        val (xs,_) = ArgsAndVis iota xBinds
        val (ys,_) = ArgsAndVis iota yBinds
        val exyBinds = buildLinTriEqs "exy" 1 (linAs,triAs) xs ys
        val AxyeBinds = splice iota [exyBinds,yBinds,xBinds,ABinds] []
        val TBinds = mkUBinds "T" "t" 0 res 1 [] []
        fun $i = vid (TBinds,Prop) ("T",i)
        fun mkfBinds ind l (aa,vv) = if ind>res then l else
            let val newf = noo ((Pi,Vis),"") ("f",ind)
                               ([],$!(fPref,MkApp (($ind,aa),vv)))
            in  mkfBinds (ind+1) (newf::l)
                         (aa@[MkApp ((Ref newf,faa),fvv)],ShowNorm::vv)
            end
        val fBinds = mkfBinds 1 [] ([],[])
        val thePref = splice iota [fBinds,TBinds] AxyeBinds
        fun $v = vid (thePref,Prop) v
        fun fix i = MkApp (($("f",i),xs),fvv)
        fun fiy i = MkApp (($("f",i),ys),fvv)
        fun mkRespApp i (AA,VV) =
            let val iLTR = Req ["lin",string_of_num lin,
                           "tri",string_of_num tri,"resp",string_of_num i]
                val (aa,vv) = ArgsAndVis iota (nthtail (thePref,2*(res-i)))
            in  (($("T",i))::(fix i)::(fiy i)::(MkApp ((iLTR,aa),vv))::AA,
                     NoShow:: NoShow:: NoShow::              ShowNorm::VV)
            end
        val theTail = if res=1 then MkApp ((Eq,[$("T",1),fix 1,fiy 1]),
                               [NoShow,ShowNorm,ShowNorm]) else
            let val ds = Req ["dep","subst",string_of_num (res-1)]
                fun mkSArgs i =
                   if i=res then ([$("T",i),fix res],[ShowNorm,ShowNorm])
                   else mkRespApp i (mkSArgs (i+1))
                val (AA,VV) = mkSArgs 1
                val lhs = MkApp ((ds,AA),VV)
                val rhs = fiy res
            in  MkApp ((Eq,[type_of_constr rhs,lhs,rhs]),
                                  [NoShow,ShowNorm,ShowNorm])
            end
        val theGoal = (thePref,theTail)
        val (oLin,oTri) = case (lin,tri)
                            of (  0,  2) => (  1,  0)
                             | (  0,  j) => (  0,j-1)
                             | (  i,  j) => (i-1,  j)
        val oTot = oLin+oTri
        val whammo = if oTot<=0 then Req ["Eq","refl"]
                     else Req ["lin",string_of_num oLin,
                               "tri",string_of_num oTri,
                               "resp",string_of_num res]
    in  if tot=0
        then let val LTR = on theGoal
                    [vooGoal [("type",1),("LTR",1)] ("goal",1),
                     vooattack ("goal",1) ("refl",1),
                     vooIntroTac ("refl",1),
                     vooRefineTac ("refl",1) "" whammo,
                     vookcatta ("goal",1)]
             in  vooQED [("type",1),("LTR",1)] tag LTR
             end
        else let val LTR = on theGoal
                    [vooGoal [("type",1),("LTR",1),("reds",1)] ("goal",1),
                     Elim MaximalStrat (Req ["Eq","J"])
                                      [("goal",1),("exy",1),("reds",1)],
                     vooattack ("subgoal",1) ("sub",1),
                     vooIntroTac ("sub",1),
                     vooRefineTac ("sub",1) "hole" whammo,
                     vooAssumption,
                     vooetastate,
                     vookcatta ("subgoal",1)]
             in  vooQED [("type",1),("LTR",1),("reds",1)] tag LTR
        end
    end
    handle _ => raise RequireFailure)
  | vooLinTriRespDemon _ = raise RequireFailure

fun vooSpecialKDemon (tag as ["special","K",N]) =
   (let val n = atoi N
        val _ = if n>1 then () else raise RequireFailure
        val (_,dsnType) = Require ["dep","subst",N]
        val (justYnLeft,_) = on ([],dsnType)
            [introvool ["A","x","y","e"] 1 n,
             fn S => vooForLoopTac
                     (fn i => ("y",i) \ ([],vid S ("x",i))) 1 (n-1) S]
        val (eqPref,AxyPref) = filter (isItA "e") justYnLeft
        val yn = Ref (hd AxyPref)
        val xn = Ref (hd (tl AxyPref))
        val PsEq = noo ((Pi,Vis),"eqn") ("eqn",1)
                       ([],MkApp ((?"%Eq%",[type_of_constr yn,xn,yn]),
                                           [NoShow,     ShowNorm,ShowNorm]))
        val PsiB = noo ((Pi,Vis),"Psi") ("Psi",1) ([PsEq],?"Type")
        val theGoal = (eqPref@(PsiB::AxyPref),?"Type")

        val EqK = ?"%Eq K%"
        fun hitEq i = Elim MaximalStrat EqK [("subgoal",1),("e",i),("reds",1)]

        val SKD = on theGoal
                  [vooGoal [("type",1),("skd",1),("reds",1)] ("subgoal",1),
                   vooForLoopTac hitEq 1 (n-1),
                   vooattack ("subgoal",1) ("gap",1),
                   vooIntroNTac (2*n+2) ("gap",1),
                   vooAssumption,
                   vookcatta ("subgoal",1)]
    in  vooQED [("type",1),("skd",1),("reds",1)] tag SKD
    end
    handle _ => raise RequireFailure)
  | vooSpecialKDemon _ = raise RequireFailure

(**)
val _ = vooDemons:=[vooDemon,vooEqJDemon,vooDepSubstDemon,vooLinTriRespDemon,
                    vooSpecialKDemon,vooEqSymDemon]
(**)