(*******************************************************************)
(******                                                       ******)
(******      The All-New Offline Dependent KJunify            ******)
(******                                                       ******)
(*******************************************************************)

val kjunify_diag = ref false

fun brack (s:string) T S =
    let val _ = if (!kjunify_diag) then message s else ()
        val S = T S
        val _ = if (!kjunify_diag) then message "bong!" else ()
    in  S
    end

fun say (s:string) S = if (!kjunify_diag) then ((message s);S) else S

val kjuElimNames = {P="p",PHI="Phi",SUBGOAL="temporary",Y="y",
                    PRED="pred",ITER="iter",A="a",H="h",EQN="eqn"}

val eqB = ref VooBase

fun updateEqB () = (eqB := unRef (Req ["Eq"]))

exception noKJunify

fun Thud () = raise noKJunify

fun deleteTac subgoal id S =
   (let val b = fetch (S?!subgoal) id
        val _ = case parseApp (ref_typ b)
                  of (Ref q,[_,l,r],_) =>
                     (case par_unif [] l r
                        of NONE => Thud ()
                         | _ => ())
                   | _ => Thud ()
    in  on S
        [Clobber MaximalStrat kjuElimNames (?"%Eq K%") (subgoal,Ref b,NONE),
         vooRename [(("temporary",1),subgoal)],
         say "!"]
    end
    handle _ => Thud ())

fun conflictTac subgoal id S =
   (let val target = pick S subgoal id
        fun bud c = case parseApp (whnf c)
                      of (Ref b,_,_) => b
                       | _ => Thud ()
        val (t,T,l,L,r,R) = case whnf (type_of_constr target)
                              of App ((_,[t,l,r]),_) =>
                                 (bud t,t,bud l,l,bud r,r)
                               | _ => Thud ()
        val (NC,NCType) = Require [ref_nam t,"no","confusion"]
        val _ = if sameRef l r then Thud () else ()
        val constructors = ref_deps t
        val _ = if member (ref_nam l) constructors then () else Thud ()
        val _ = if member (ref_nam r) constructors then () else Thud ()
        val (_,aa,_) = parseApp (whnf T)
        val nTargs = length aa  (* params + indices *)
        val (NCPref,_) = introall iota "z" 1 ([],NCType)
        val dep = ((length NCPref)-nTargs-1) div 2  (* dependency level *)
        val (_,vv) = ArgsAndVis iota NCPref
        fun cutIt [] = (dep-1,[],[])
          | cutIt (h::t) =
            let val (i,f,b) = cutIt t
            in  if i=0 then (0,h::f,b) else (i-1,[],h::b)
            end
        val (_,params,indices) = cutIt aa
        val eqr = ?"%Eq refl%"
        val refls = map (fn a => App ((eqr,[type_of_constr a,a]),
                                           [NoShow,ShowNorm])) indices
        val NCargs = params@(splice iota [indices,indices,refls]
                             [L,R,target])
        val trick = App ((NC,NCargs),vv)
    in  on S [vooattack subgoal ("doomed",1),
              vooIntroTac ("doomed",1),
              vooRefineTac ("doomed",1) "" trick,
              vookcatta subgoal,
              say "!"]
    end
    handle _ => Thud ())

fun injectTac subgoal id S =
   (let val subgB = fetch S subgoal
        val (subgPref,subgTail) = case ref_kind (subgB)
                                    of Voo (_,D) => D
                                     | _ => Thud ()
        val (above,tarB,below) = vooctxtrec
            {hitBot = fn _ => ([],VooBase,[]), hitDom = voocontinue,
             hitVoo = fn (jd,_) => fn b => fn _ => fn rect =>
                      let val (ab,c,be) = rect ()
                      in  if jd=id then ([b],b,be)
                          else if ab=[] then ([],c,b::be) else (b::ab,c,be)
                      end} subgPref
        val reallyAbove = except_last above
        fun bud c = case parseApp (whnf c)
                      of (Ref b,_,_) => b
                       | _ => Thud ()
        val (t,T,l,L,r,R) = case whnf (ref_typ tarB)
                              of App ((_,[t,l,r]),_) =>
                                 (bud t,t,bud l,l,bud r,r)
                               | _ => Thud ()
        val (NC,NCType) = Require [ref_nam t,"no","confusion"]
        val _ = if sameRef l r then () else Thud ()
        val constructors = ref_deps t
        val _ = if member (ref_nam l) constructors then () else Thud ()
        val (_,aa,_) = parseApp (whnf T)
        val nTargs = length aa  (* params + indices *)
        val (NCPref,_) = introall iota "z" 1 ([],NCType)
        val dep = ((length NCPref)-nTargs-1) div 2  (* dependency level *)
        val (_,vv) = ArgsAndVis iota NCPref
        fun cutIt [] = (dep-1,[],[])
          | cutIt (h::t) =
            let val (i,f,b) = cutIt t
            in  if i=0 then (0,h::f,b) else (i-1,[],h::b)
            end
        val (_,params,indices) = cutIt aa
        val topEnd = (above,subgTail)
        val _ = ldify tarB
        val Psi = $!topEnd
        val _ = pify tarB
        val eqr = ?"%Eq refl%"
    in  if dep>1 andalso voobin tarB topEnd then (* really nasty *)
    let val Phi = if dep=1 then Psi
                  else synthApp (Req ["special","K",string_of_num dep])
                                Psi ShowNorm
        val refls = map (fn a => App ((eqr,[type_of_constr a,a]),
                                           [NoShow,ShowNorm])) indices
        val NCargs = params@(splice iota [indices,indices,refls]
                             [L,R,Ref tarB,Phi])
        val trick = App ((NC,NCargs),vv@[ShowNorm])
        val ind = vooConj S subgoal (fn S => safeNumberScope S (#1 id) 1)
        val (trickInfo,_) = on (start (type_of_constr trick))
                            [vooin ("Hyp",1),
                             voodom ("Hyp",1),
                             introall iota "e" ind,
                             domvoo ("Hyp",1)]
        val (newEqs,grot) = case ref_kind (hd trickInfo)
                              of Voo (_,D) => D
                               | _ => Thud ()
        val Dafter = (newEqs@below,grot)
        val newSB =  noo (HoleBV,ref_nam subgB) subgoal Dafter
        val (ldas,(zap,paz)) = copyCtxt ldify (tarB::below)
        val (paa,pvv) = ArgsAndVis iota ldas
        val thePloy = (ldas@[newSB],
                       MkApp ((zap%>>trick,[MkApp ((Ref newSB,paa),pvv)]),
                                           [ShowNorm]))
    in  say "!" ((subgoal\thePloy) S)
    end else
    let val Phi = if dep=1 then Psi
                  else let val (ps,indBits) = introvool ["bunk"] 1
                                              (length params) ([],ref_typ t)
                           val (indTys,_) = introvool ["ind"] 1 (dep-1)
                                            ([],indBits)
                           val (triInds,_,_) = triang indTys
                           val tt = triInds@[MkApp ((Ref t,params),
                                                    #2 (ArgsAndVis iota ps))]
                           val ll = indices@[L]
                           val rr = indices@[R]
                           val dummies = triEqs "dummy" 1 tt ll rr []
                       in  $!(reallyAbove@(map ldify dummies),subgTail)
                       end
        val refls = map (fn a => App ((eqr,[type_of_constr a,a]),
                                           [NoShow,ShowNorm])) indices
        val NCargs = params@(splice iota [indices,indices,refls]
                             [L,R,Ref tarB,Phi])
        val trick = App ((NC,NCargs),vv@[ShowNorm])
        val ind = vooConj S subgoal (fn S => safeNumberScope S (#1 id) 1)
        val (trickInfo,_) = on (start (type_of_constr trick))
                            [vooin ("Hyp",1),
                             voodom ("Hyp",1),
                             introall iota "e" ind,
                             domvoo ("Hyp",1)]
        val (newEqs,oldEq) = case ref_kind (hd trickInfo)
                               of Voo (_,(dc,App ((_,l),_))) => (dc,last l)
                                | _ => Thud ()
        val (topC,topT) = if dep=1 then (id\ ([],oldEq)) topEnd
                          else (reallyAbove,subgTail)
        val Dafter = (topC@newEqs@below,topT)
        val newSB =  noo (HoleBV,ref_nam subgB) subgoal Dafter
        val (ldas,(zap,paz)) = copyCtxt ldify (tarB::below)
        val (paa,pvv) = ArgsAndVis iota (tl ldas)
        val thePloy = (ldas@[newSB],
                       MkApp ((zap%>>trick,[MkApp ((Ref newSB,paa),pvv)]),
                                           [ShowNorm]))
    in  say "!" ((subgoal\thePloy) S)
    end
    end
    handle _ => Thud ())

fun checkTac subgoal id S =
   (let val targ = pick S subgoal id
        val (theType,theNeedle,theHaystack,leftFlag) =
            case whnf (type_of_constr targ)
              of App ((q,[t,l,r]),_) =>
                 let val _ = if sameTerm q (?"%Eq%") then () else Thud ()
                     val _ = if sameTerm l r then Thud () else ()
                 in  case l
                       of Ref b => (t,b,r,true)
                        | _ => case r
                                 of Ref b => (t,b,l,false)
                                  | _ => Thud ()
                 end
               | _ => Thud ()
        val (tyF,tyA,tyV) = parseApp theType
        fun bdHead c = case voohead (whnf c) of Ref b => b | _ => Thud ()
        val typeBd = bdHead theType
        val conList = ref_deps typeBd
        val conTypes = map % conList
        val mutTypeBds = map bdHead conTypes
        val mutTypeNames = map ref_nam mutTypeBds
        fun recSpot i (Bind (_,_,dom,ran)) =
            if (member (ref_nam (bdHead dom)) mutTypeNames) handle _ => false
            then i::(recSpot (i+1) ran)
            else 0::(recSpot i ran)
          | recSpot _ _ = []
        val conRecInfo = map (recSpot 1) conTypes
            (* We mark each constructor argument position with 0
               if it's nonrecursive, or by the index of its iterate *)
        val conNums = mkList iota 1 (length conList)

        exception notHere
        fun findPath (Ref b) = if sameRef b theNeedle then []
                               else raise notHere
          | findPath t =
            let val (f,aa,_) = parseApp (whnf t)
                val fnam = case f of Ref b => ref_nam b | _ => raise notHere
                val struc = zAssoc conList conRecInfo fnam
                            handle Assoc => raise notHere
                val num = zAssoc conList conNums fnam
                fun search (0::st) (ah::at) = search st at
                  | search (n::st) (ah::at) = ((num,n)::(findPath ah)
                    handle notHere => search st at)
                  | search _ _ = raise notHere
            in  search struc aa
            end
        val thePath = findPath theHaystack
        val depth = length thePath
        val nat = ?"%nat%"
        val zero = ?"%nat zero%"
        val suc = ?"%nat suc%"
        fun mkTT [_] = nat
          | mkTT (_::t) = Bind ((Sig,Vis),"",nat,mkTT t)
          | mkTT [] = Thud ()
        val trickType = mkTT thePath
        local (* why is projection so nasty? *)
            fun last 1 t = t
              | last n t = last (n-1) (Proj (Snd,t))
        in  fun myproj n t =
                if n=depth then last n t else if n=1 then Proj (Fst,t)
                else myproj (n-1) (Proj (Snd,t))
        end
        fun trickRecTerm n t =  (* grab projection; timely increment *)
            if n=depth then App ((suc,[myproj 1 t]),[ShowNorm])
            else myproj (n+1) t
        val (indPref,_) = introall iota "i" 1 ([],ref_typ typeBd)
        val (taa,tvv) = ArgsAndVis iota indPref
        val tarB = noo ((Pi,Vis),"x") ("t",1) ([],MkApp ((Ref typeBd,taa),tvv))
        val theGoal = (tarB::indPref,trickType)

        fun solveSubg i S =
            let val S' = on S
                         [vooattack ("subgoal",i) ("zob",1),
                          vooIntroTac ("zob",1)]
                fun conTupL n [] = []
                  | conTupL n ((j,ind)::t) = (if i=j (* on the path? *)
                    then trickRecTerm n (vid S' ("iter",ind))
                    else zero)::(conTupL (n+1) t) (* zeros off path *)
                val tupL = conTupL 1 thePath
                val zob = ([],if depth=1 then hd tupL
                              else Tuple (trickType,tupL))
            in  on S' [("zob",1)\zob,
                       vookcatta ("subgoal",i)]
            end
        fun solvePhi i S = on S [vooattack ("Phi",i) ("zob",1),
                                 vooIntroTac ("zob",1),
                                 vooRefineTac ("zob",1) "" trickType,
                                 vookcatta ("Phi",i)]
        val TRICK = on theGoal
                    [vooGoal [("type",1),("trick",1)] ("goal",1),
                     Elim MaximalStrat (Req [ref_nam typeBd,"elim"])
                          [("goal",1),("t",1)],
                     vooSubSequence "Phi" solvePhi,
                     vooSubSequence "subgoal" solveSubg]
        val guts = MkApp ((ref_val (fetch TRICK ("trick",1)),tyA),tyV)
        val trick = vooeta (Bind ((Lda,Vis),"q",theType,
                                myproj 1 (MkApp ((guts,[Rel 1]),[ShowNorm]))))
        val badEq = MkApp ((synthApp (?"%lin 1 tri 0 resp 1%") targ ShowNorm,
                            [nat,trick]),[NoShow,ShowNorm])
        val nEqSucN = if leftFlag then badEq
                      else synthApp (?"%Eq sym%") badEq ShowNorm
        val Absurd = synthApp (?"%nat no cycles%") nEqSucN ShowNorm
    in  on S [vooattack subgoal ("zob",1),
              vooIntroTac ("zob",1),     (* used to be up to id *)
              vooRefineTac ("zob",1) "" Absurd,
              vookcatta subgoal,
              say "!"]
    end
    handle _ => Thud ())

fun eliminateTac subgoal id S =
   (let val target = pick S subgoal id
        val (l,r) = case whnf (type_of_constr target)
                      of App ((_,[_,l,r]),_) => (whnf l,whnf r)
                       | _ => Thud ()
        val S' = voodom subgoal S
        fun chk (Ref b) = (vooctxtrec
                           {hitBot = fn _ => false,
                            hitDom = fn _ => fn _ => fn _ => fn _ => false,
                            hitVoo = fn _ => fn c => fn _ => fn rect =>
                                     sameRef b c orelse rect ()} (#1 S'))
          | chk _ = false
        val direct = if chk r then SOME true
                     else if chk l then SOME false
                     else NONE
        val S = domvoo subgoal S'
        val _ = if (sameTerm l r) then Thud () else ()
    in  case direct
          of NONE => Thud ()
           | SOME true =>
            (case r
               of Ref b =>
                  if depends b l
                  then checkTac subgoal id S
                  else on S
                       [Clobber MaximalStrat kjuElimNames (?"%Eq J%")
                                (subgoal,target,NONE),
                        vooRename [(("temporary",1),subgoal)],
                        say "!"]
                | _ => Thud ())
           | SOME false =>
            (case l
               of Ref b =>
                  if depends b r
                  then checkTac subgoal id S
                  else on S
                       [Clobber MaximalStrat kjuElimNames (?"%Eq J sym%")
                                (subgoal,target,NONE),
                        vooRename [(("temporary",1),subgoal)],
                        say "!"]
                | _ => Thud ())
    end
    handle _ => Thud ())

fun KJunifyOneTac subgoal id S =
   (let val _ = say "?" ()
        val test = sameRef (!eqB)
                  (unRef (voohead (ref_typ (fetch (S?!subgoal) id))))
        val _ = say ";" ()
    in
    if test
    then brack "del.. " (deleteTac subgoal id) S
         handle noKJunify =>
         brack "elim.. " (eliminateTac subgoal id) S
         handle noKJunify =>
         brack "check.. " (checkTac subgoal id) S
         handle noKJunify =>
         brack "conf.. " (conflictTac subgoal id) S
         handle noKJunify =>
         brack "inj.. " (injectTac subgoal id) S
    else raise noKJunify
    end
    handle _ => raise noKJunify)

fun KJunifyTestMoreDoneIntros test subgoal S = (* always succeeds *)
   (let
        val b = fetch S subgoal
        val dc = case ref_kind b
                   of Voo (_,(dc,_)) => dc
                    | _ => failwith "disaster"
    in (vooctxtrec
        {hitBot = fn _ => Thud (), hitDom = voocontinue,
         hitVoo = fn (id,_) => fn b => fn _ => fn rect =>
                  rect ()
                  handle noKJunify =>
                  if test b then KJunifyTestMoreDoneIntros test subgoal
                                 (KJunifyOneTac subgoal id S)
                  else Thud ()} dc)
        handle noKJunify => say "." S
    end
    handle missing_voodoo => S)

fun KJunifyTestMore test subgoal S = (* always succeeds *)
   (let val _ = updateEqB ()
        val S = on S
                [voodom subgoal,
                 fn S => introtestall (Okras Pi) dnf "prem"
                         (safeNumber S "prem" 1) S,
                 domvoo subgoal]
    in  let
        val b = fetch S subgoal
        val dc = case ref_kind b
                   of Voo (_,(dc,_)) => dc
                    | _ => failwith "disaster"
    in (vooctxtrec
        {hitBot = fn _ => Thud (), hitDom = voocontinue,
         hitVoo = fn (id,_) => fn b => fn _ => fn rect =>
                  rect ()
                  handle noKJunify =>
                  if test b then KJunifyTestMoreDoneIntros test subgoal
                                 (KJunifyOneTac subgoal id S)
                  else Thud ()} dc)
        handle noKJunify => say "." S
    end 
    handle missing_voodoo => S
    end
    handle missing_voodoo => S)

fun KJunifyTestTac test subgoal S = (* must make some progress *)
    let val _ = updateEqB ()
        val S = on S
                [say "introducing.. ",
                 voodom subgoal,
                 fn S => introtestall (Okras Pi) dnf "prem"
                         (safeNumber S "prem" 1) S,
                 domvoo subgoal,
                 say "kjunify!\n"]
    in  let
        val b = fetch S subgoal
        val dc = case ref_kind b
                   of Voo (_,(dc,_)) => dc
                    | _ => failwith "disaster"
    in  vooctxtrec
        {hitBot = fn _ => Thud (), hitDom = voocontinue,
         hitVoo = fn (id,_) => fn b => fn _ => fn rect =>
                  rect ()
                  handle noKJunify =>
                  if test b then KJunifyTestMoreDoneIntros test subgoal
                                 (KJunifyOneTac subgoal id S)
                  else Thud ()} dc
    end end

fun KJunifyStep subgoal S =
    let val S = on S
                [voodom subgoal,
                 fn S => introall dnf "prem" (safeNumber S "prem" 1) S,
                 domvoo subgoal]
    in  let
        val b = fetch S subgoal
        val dc = case ref_kind b
                   of Voo (_,(dc,_)) => dc
                    | _ => failwith "disaster"
    in  vooctxtrec
        {hitBot = fn _ => Thud (), hitDom = voocontinue,
         hitVoo = fn (id,_) => fn b => fn _ => fn rect =>
                  rect ()
                  handle noKJunify =>
                  KJunifyOneTac subgoal id S} dc
    end end

fun KJunifyNameTac name = KJunifyTestTac
    (fn b => (#1 (bid b))=name handle _ => false)

val KJunifyTac = KJunifyTestTac (const true)

(* simplifyPremise uses KJunify to reduce equational constraints in
   the premise of a subgoal; the polarity is opposite, but the
   effect looks the same; the idea is essentially that
     (i) a premise which requires inconsistent constraints to be
           satisfied is no use anyway
    (ii) completeness guarantees that the reduced equations have
           the same solutions as the original set *)

fun simplifyPremise subg prem S =
    let val what = pick S subg prem
        val D = case what
                  of Ref b => (case ref_kind b
                                 of Voo (_,D) => D
                                  | _ => failwith "you got me")
                   | _ => raise missing_voodoo
        val (C,T) = introall dnf "prem" (safeNumber S "prem" 1) D
        val (copyC,(zap,_)) = copyCtxt iota C
        val T' = zap%>>T
        val (aa,vv) = ArgsAndVis iota copyC
        val hack = Bind ((Pi,Vis),"what",T',Prop)
        val hackRef = noo ((Pi,Vis),"hack") ("hack",1) ([],hack)
        val just = App ((Ref hackRef,[MkApp ((what,aa),vv)]),[ShowNorm])
        val justRef = noo ((Pi,Vis),"just") ("just",1) ([],just)
        val bef = ([noo (HoleBV,"spiter") ("spiter",1)
                        (justRef::hackRef::copyC,T')],
                   Prop)
        val (response,_) = KJunifyTestMore (const true) ("spiter",1) bef
        val Sref = fetch S subg
        val (SC,ST) = case ref_kind Sref
                        of Voo (_,D) => D
                         | _ => failwith "you got me!"
        val (premise,(prior,post)) = vooctxtrec
            {hitBot = fn _ => (VooBase,([],[])),
             hitDom = voocontinue,
             hitVoo = fn (id,_) => fn b => fn t => fn rect =>
                      if id=prem then (b,(t,[]))
                      else (iota**(iota**(cons b))) (rect ())} SC
    in  case response
          of [] => let val newSubg = (post@prior,ST)
                       val (ldas,_) = copyCtxt ldify (premise::prior)
                       val (aa,vv) = ArgsAndVis iota (tl ldas)
                       val newRef = noo (HoleBV,ref_nam Sref) subg newSubg
                       val solver = (ldas@[newRef],App ((Ref newRef,aa),vv))
                   in  (subg \ solver) S
                   end
           | [b] => (case ref_kind b
                       of Voo (_,(RC,NT)) =>
                          let val (NC,trick) = vooctxtrec
                                  {hitBot = fn _ => ([],Bot),
                                   hitDom = voocontinue,
                                   hitVoo = fn (id,(_,DT)) => fn b => fn _ =>
                                            fn rect =>
                                           (if id=("hack",1) then iota
                                            else if id=("just",1)
                                            then case DT
                                                   of App ((_,[x]),_) =>
                                                      iota**(const x)
                                                    | _ => failwith "oops!"
                                            else (cons b)**iota) (rect ())} RC
                              val newPrem = noo ((ref_bind premise,
                                                  ref_vis premise),
                                                 ref_nam premise)
                                                prem (NC,NT)
                              val (ldas,(zap,_)) =
                                  copyCtxt ldify (premise::prior)
                              val (aa,vv) = ArgsAndVis iota (tl ldas)
                              val newSubg = (post@(newPrem::prior),ST)
                              val newRef = noo (HoleBV,ref_nam Sref) subg newSubg
                              val (Nldas,(zap2,_)) = copyCtxt ldify NC
                              val just = zap%>>($!
                                         (vooetastate (Nldas,zap2%>>trick)))
                              val nearly = vooetastate (ldas,
                                            App ((Ref newRef,aa@[just]),
                                                 vv@[prVis (ref_vis premise)]))
                              val solver = ((#1 nearly)@[newRef],#2 nearly)
                          in  (subg \ solver) S
                          end
                        | _ => failwith "you got me!")
           | _ => S
    end

fun LegoKJunify1 () =
    vooLegoRefine [("type",1),("blah",1)]
    (KJunifyStep ("goal",1) (vooStealGoal [("type",1),("blah",1)] ("goal",1)))

fun LegoKJunify () =
    vooLegoRefine [("type",1),("blah",1)]
    (KJunifyTac ("goal",1) (say "goal\n" (brack "getting.. "
     (vooStealGoal [("type",1),("blah",1)]) ("goal",1))))

fun findPrem subgoal id s i S =
    let val T = vooConj S subgoal (#2)
        exception shesNotThere
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
        val howMany = ((case i
                          of 0 => get_name 1
                           | i => get_num 1 1) T)-1
    in  on S [voodom subgoal,
              fn S => introvool ["prem"] (safeNumber S "prem" 1) howMany S,
              vooin id,
              domvoo subgoal]
    end

fun LegoElim c i rule = 
    let val S = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
                [findPrem ("goal",1) ("target",1) c i,
                 Elim MaximalStrat rule [("goal",1),("target",1)]]
    in  vooLegoRefine [("type",1),("blah",1)] S
    end

fun LegoElimKJunify c i rule = 
    let fun hitSub i S = on S
            [KJunifyTestMore (const true) ("subgoal",i),
             vooSubSubSequence ("subgoal",i) "iter" simplifyPremise]
        val S = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
                [findPrem ("goal",1) ("target",1) c i,
                 Elim MaximalStrat rule [("goal",1),("target",1)],
                 vooSubSequence "subgoal" hitSub]
    in  vooLegoRefine [("type",1),("blah",1)] S
    end

fun Stratocaster "lex" = RightStrat
  | Stratocaster "mid" = MiddleStrat
  | Stratocaster "min" = MinimalStrat
  | Stratocaster "max" = MaximalStrat
  | Stratocaster _ = MaximalStrat

fun LegoInduction st c i =
    let val S = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
                [findPrem ("goal",1) ("target",1) c i]
        val ty = vooConj S ("goal",1) (fn S => ref_typ (fetch S ("target",1)))
        val tyN = case voohead (dnf ty)
                    of Ref b => ref_nam b
                     | _ => failwith "can't apply induction"
        fun hitSub i S = on S
            [KJunifyTestMore (const true) ("subgoal",i),
             vooSubSubSequence ("subgoal",i) "iter" simplifyPremise]
        val S = on S [Elim (Stratocaster st) (Req [tyN,"elim"])
                         [("goal",1),("target",1)],
                      vooSubSequence "subgoal" hitSub]
    in  vooLegoRefine [("type",1),("blah",1)] S
    end

fun LegoCases st c i =
    let val S = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
                [findPrem ("goal",1) ("target",1) c i]
        val ty = vooConj S ("goal",1) (fn S => ref_typ (fetch S ("target",1)))
        val tyN = case voohead (dnf ty)
                    of Ref b => ref_nam b
                     | _ => failwith "can't apply induction"
        fun hitSub i S = on S
            [KJunifyTestMore (const true) ("subgoal",i),
             vooSubSubSequence ("subgoal",i) "iter" simplifyPremise]
        val S = on S [Elim (Stratocaster st) (Req [tyN,"cases"])
                         [("goal",1),("target",1)],
                      vooSubSequence "subgoal" hitSub]
    in  vooLegoRefine [("type",1),("blah",1)] S
    end

fun LegoInvert (targ,targTy) =
    let val tyN = case voohead (dnf targTy)
                    of Ref b => ref_nam b
                     | _ => failwith "can't apply induction"
        fun hitSub i = KJunifyTestMore (const true) ("subgoal",i)
        val S = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
                   [Clobber MaximalStrat usualElimNames (Req [tyN,"cases"])
                         (("goal",1),targ,NONE),
                      vooSubSequence "subgoal" hitSub]
    in  vooLegoRefine [("type",1),("blah",1)] S
    end

fun maybeTac id blat S =
    (((fetch S id);(blat S)) handle missing_voodoo => S)

fun ElimKJunify strat rule subg targ S =
    let val target = pick S subg targ
        val (sgsg,S) = holyClobber strat usualElimNames true rule
                                  (subg,target,NONE) S
        fun hitSub b S =
            let val id = bid b
            in  on S
               [KJunifyTestMore (const true) id,
                maybeTac id
                 (vooSubSubSequence id "iter" simplifyPremise)]
            end
    in  foldr hitSub S sgsg
    end
