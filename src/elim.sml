open ConorRequire

datatype elimPiStrategy = MaximalStrat (* many Pis under the elim *)
                        | MiddleStrat  (* everything depending on index vars *)
                        | MinimalStrat (* just the critical things *)
                        | MissingStrat of (string * int) list (* some out *)
                        | RightStrat   (* index vars and stuff to right *)

exception noClobber

val parselimDebug = ref false
val clobberDebug = ref false
val clobberDiag = ref true

type elimComponentNames =
     {P:string,PHI:string,SUBGOAL:string,Y:string,
      PRED:string,ITER:string,A:string,H:string,EQN:string}

val usualElimNames = {P="p",PHI="Phi",SUBGOAL="subgoal",Y="y",
                      PRED="pred",ITER="iter",A="a",H="h",EQN="eqn"}

fun parselim S ({P,PHI,SUBGOAL,Y,PRED,ITER,A,H,EQN}:elimComponentNames)
             elimType =
    let val (e1C,e1T) = introall whnfLetBlat
                        "d" 1 (start elimType) (* d for dunno *)
        val depth = case ref_kind (hd e1C)
                      of Voo ((_,d),_) => d
                       | _ => failwith "not an elimination rule"

        val _ = if (!parselimDebug)
                then ((print "parselim input:\n");
                      (vooprintstate (e1C,e1T));
                      (print "\n"))
                else ()

        (* we can spot the main Phi by looking at the tail *)
        val (phiF,phiA,phiV) = parseApp e1T
        val (_,phind) = tid phiF
                        handle missing_voodoo =>
                        failwith "not an elimination rule"
        val e2Plan = vooRename [(("d",phind),(PHI,phind))] (e1C,e1T)

        val _ = if (!parselimDebug)
                then ((print "parselim found main Phi:\n");
                      (vooprintstate e2Plan);
                      (print "\n"))
                else ()

        (* find the indices, bot not necessarily the targetter (think rels) *)
        val phargids = foldr (fn a => fn l => (tid a)::l
                                              handle missing_voodoo => l)
                             [] phiA
        val (e3C,e3T) = vooRename (map (fn (_,i) => (("d",i),(Y,i))) phargids)
                        e2Plan

        val _ = if (!parselimDebug)
                then ((print "parselim found phargids:\n");
                      (vooprintstate (e3C,e3T));
                      (print "\n"))
                else ()

        (* find the Phis *)
        fun getem S [] l = (S,l)
          | getem S (b::t) l =
           (case bid b
              of (id as ("d",i)) =>
                 if i<=phind then (S,l)
                 else
                 let val S' = on S [voodom id,
                                    introall whnf A 1]
                     val (f,a,v) = parseApp (#2 S')
                 in  let val phid = tid f
                     in  getem (domvoo id S') t (union [phid] l)
                     end
                     handle missing_voodoo => getem (domvoo id S') t l
                 end
               | (_,i) => if i>phind then getem S t l else (S,l))
            handle missing_voodoo => (S,l)
        val (e3',dsforPhis) = getem (e3C,e3T) e3C []
        val (e4C,e4T) =
            vooRename (map (fn (_,i) => (("d",i),(PHI,i))) dsforPhis) e3'

        val _ = if (!parselimDebug)
                then ((print "parselim found Phis:\n");
                      (vooprintstate (e4C,e4T));
                      (print "\n"))
                else ()

        (* find ps, subgoals; renumber *)
        val (p,y,Phi,subgoal) = (safeNumber S P 1,
                                 safeNumber S Y 1,
                                 safeNumber S PHI 1,
                                 safeNumber S SUBGOAL 1)
        fun getem [] = ((e4C,e4T),[],p,y,Phi,subgoal)
          | getem (b::t) =
            let val id as (s,i) = bid b
            in  assoc s
                 [("d",fn () =>
                     let val (S,l,p,y,Phi,subgoal) = getem t
                         val (f,_,_) = case ref_kind b
                                         of Voo (_,(_,t)) => parseApp t
                                          | _ => failwith "bungled it!"
                         val (id',p,subgoal) =
                             ((if (#1 (tid f))=PHI
                               then ((SUBGOAL,subgoal),p,subgoal+1)
                               else raise missing_voodoo)
                               handle missing_voodoo =>
                               ((P,p),p+1,subgoal))
                     in (S,(id,id')::l,p,y,Phi,subgoal)
                     end),
                  (Y,fn () =>
                     let val (S,l,p,y,Phi,subgoal) = getem t
                     in  (S,(id,(Y,y))::l,p,y+1,Phi,subgoal)
                     end),
                  (PHI,fn () =>
                     let val (S,l,p,y,Phi,subgoal) = getem t
                         val S' = if i>phind then S (* intros already done *)
                                  else on S [voodom id,
                                             introall whnf A 1,
                                             domvoo id]
                     in  (S',(id,(PHI,Phi))::l,p,y,Phi+1,subgoal)
                     end)] ()
                 handle Assoc => failwith "parselim acting up!"
            end
            handle missing_voodoo => ((e4C,e4T),[],p,y,Phi,subgoal)
        val (e4',dsforstuff,_,_,_,subgPlus1) = getem e4C
        val e5Plan = vooRename dsforstuff e4'

        val _ = if (!parselimDebug)
                then ((print "parselim top layer:\n");
                      (vooprintstate e5Plan);
                      (print "\n"))
                else ()

        (* parse the subgoals *)
        val (h1,pred1,iter1) = (safeNumber S H 1,safeNumber S PRED 1,
                                                 safeNumber S ITER 1)
        fun hitas (S as (ctxt,tail)) =
            let fun getem [] = (S,[],pred1,iter1)
                  | getem (b::t) =
                    let val (S,l,pred,iter) = getem t
                        val id = bid b
                        val S' = on S [voodom id,
                                       introall whnf H h1]
                        val (f,a,v) = parseApp (#2 S')
                        val S' = domvoo id S'
                        val (id',pred,iter) =
                            (if (#1 (tid f))=PHI
                             then ((ITER,iter),pred,iter+1)
                             else ((PRED,pred),pred+1,iter))
                            handle missing_voodoo =>
                            ((PRED,pred),pred+1,iter)
                    in  (S',(id,id')::l,pred,iter)
                    end
                    handle missing_voodoo => (S,[],pred1,iter1)
                val (S',hitlist,_,_) = getem ctxt
            in  vooRename hitlist S'
            end
        fun doSubg i S =
            if i=subgPlus1 then S
            else on S [doSubg (i+1),
                       voodom (SUBGOAL,i),
                       hitas,
                       domvoo (SUBGOAL,i)]
        val e6Plan = doSubg subgoal e5Plan

        val _ = if (!parselimDebug)
                then ((print "parselim subgoals:\n");
                      (vooprintstate e6Plan);
                      (print "\n"))
                else ()

    in  e6Plan
    end

local

    exception noReds

    fun Thud () = failwith "bug in reduction code"

    fun getRedInfo (Ref elimRef) (problem,SOME redId,subgoal) =
       (let val elimReds = get_reductions elimRef
                           handle Assoc => raise noReds
            val redProb = voodom redId problem
                          handle missing_voodoo => raise noReds
            val redWhich = vooctxtrec
                {hitBot = fn t => [],
                 hitDom = fn _ => fn b => fn t => fn _ => [],
                 hitVoo = fn (id,(_,dt)) => fn b => fn t => fn rect =>
                        ((case dt
                            of (CnLst [LabVT (RedPr,_,rhs)]) =>
                               if (tid (voohead rhs))=subgoal
                               then cons id
                               else iota
                             | _ => iota)
                         handle missing_voodoo => iota) (rect ())}
                (#1 redProb)
            val _ = domvoo redId redProb
        in  SOME {elimReds=elimReds,
                  redId=redId,
                  redWhich=redWhich}
        end
        handle noReds => NONE)
      | getRedInfo _ _ = NONE

    fun proformas safeIn nom S =
        let val nom1 = safeNumber S nom (safeNumber safeIn nom 1)
            fun inLda i (S as (_,Bind ((Lda,_),_,_,_))) =
                inLda (i+1) (vooin (nom,i) S)
              | inLda _ x = x
            val (C,l,nomn) = case (inLda nom1 S)
                               of (C as h::_,CnLst l) => (C,l,1+(#2 (bid h)))
                                | ([],CnLst l) => ([],l,1)
                                | _ => raise noReds
            fun doOne (LabVT (RedPr,lhs,rhs)) =
                let val (rC,rT) = inLda nomn ([],rhs)
                    val (raa,rvv) = ArgsAndVis iota rC
                    val (theC,(zap,_)) = copyCtxt pihole (rC@C)
                in  cons (theC,zap%>>(MkApp ((lhs,raa),rvv)),zap%>>rT)
                end
              | doOne _ = iota
        in  foldr doOne [] l
        end

    fun unfold (oC,oL,oR) (iC,iL,iR) =
        let val (oF,oAA,oVV) = parseApp oR
            val (iF,iAA,iVV) = parseApp iL
            val _ = if sameTerm oF iF then () else raise noReds
            val (oC,oL,oAA) =
                if oC=[] then ([],oL,oAA)
                else let val (oC,(zap,_)) = copyCtxt iota oC
                     in  (oC,zap%>>oL,map (fn t => zap%>>t) oAA)
                     end
            val (iC,iR,iAA) =
                if iC=[] then ([],iL,iAA)
                else let val (iC,(zap,_)) = copyCtxt iota iC
                     in  (iC,zap%>>iR,map (fn t => zap%>>t) iAA)
                     end
            fun doArgs sbst aa vv [] _  = (#1 (sbst$>>>(iC@oC,Prop)),
                                  sbst$>>oL, sbst$>>(MkApp ((iR,aa),vv)))
              | doArgs sbst [] _  aa vv = (#1 (sbst$>>>(iC@oC,Prop)),
                sbst$>>(MkApp ((oL,aa),vv)), sbst$>>iR)
              | doArgs sbst (oah::oat) (_::ovt) (iah::iat) (_::ivt) =
               (case par_unif sbst (sub sbst oah) (sub sbst iah)
                  of SOME s => doArgs s oat ovt iat ivt
                   | NONE => raise noReds)
              | doArgs _ _ _ _ _ = raise noReds
        in  doArgs [] oAA oVV iAA iVV
        end

    fun foldRew (oC,oL,oR) =
        let val (oF,oAA,oVV) = parseApp oR
            fun go _ tm =
               (let val (iF,iAA,iVV) = parseApp tm
                    val _ = if sameTerm oF iF then () else raise noReds
                    val tmVars = voodep1l tm
                    val (oC,oL,oAA) =
                        if oC=[] then ([],oL,oAA)
                        else let val (oC,(zap,_)) = copyCtxt iota oC
                             in  (oC,zap%>>oL,map (fn t => zap%>>t) oAA)
                             end
                    fun doArgs sbst ldas [] _ aa vv =
                        sbst$>>($!(ldas,MkApp ((oL,aa),vv)))
                      | doArgs sbst ldas (oaa as oah::oat) ovv [] _ =
                        let val e = noo ((Lda,Vis),"") ("eta",1)
                                        ([],type_of_constr (sbst$>>oah))
                        in  doArgs sbst (e::ldas) oaa ovv [Ref e] [ShowNorm]
                        end
                      | doArgs sbst l (oah::oat) (_::ovt) (iah::iat) (_::ivt) =
                       (case par_unif sbst (sub sbst oah) (sub sbst iah)
                          of SOME s => doArgs s l oat ovt iat ivt
                           | NONE => raise noReds)
                      | doArgs _ _ _ _ _ _ = raise noReds
                    val replacement = doArgs [] [] oAA oVV iAA iVV
                in  if voofold false (fn a => fn b => a orelse b)
                               (fn b => holy b
                                andalso (not (member (bid b) tmVars)))
                               replacement
                    then UMod
                    else Mod replacement
                end handle noReds => UMod)
        in  go
        end

    fun narrow outer inner =
        let val (C,L,R) = unfold outer inner
            val R = (foldRew outer)>>(varFix (dnf R))
            val (fL,aL,vL) = parseApp L
            fun bobbit [] _ ldas old = (old,ldas)
              | bobbit aa vv ldas old =
                let val (al,ab) = sep_last aa
                    val (vl,vb) = sep_last vv
                in  case al
                      of Ref b => if holy b then
                         let val bob = MkApp ((fL,ab),vb)
                         in  if depends b bob
                             then (old,ldas)
                             else bobbit ab vb ((holeldav b)::ldas) bob
                         end else (old,ldas)
                       | _ => (old,ldas)
                end
            val (L,Rldas) = bobbit aL vL [] L
            val red = LabVT (RedPr,L,$!(vooetastate (Rldas,R)))
            val (C,_) = vooctxtdepfilter C [red]
        in  (vootopsort (map holeldav C),CnLst[red])
        end

    fun MrFreeze f (S as (C,_)) = ((vooctxtrec
       {hitBot = fn _ => (), hitDom = voocontinue,
        hitVoo = fn _ => fn b => fn _ => fn rect =>
                ((if (#1 (ref_bd b))=HoleBV then (ref_frz b):=f else ());
                 (rect ()))} C);S)

    fun narrowReds modProb {elimReds,redId,redWhich} =
       (let val redProb as (redPref,_) = on modProb
                                            [MrFreeze Froz, voodom redId]
            val nextRedNum = safeNumber redProb "red" 1
            val innerProfs = proformas redProb "i" ([],elimReds)
            fun gluon h (C,i) =
                let val b = ((Sig,VBot),"",Bot,Bot):!(Voo (("red",i),h))
                in  (b::C,i+1)
                end
            val (doneReds,_) = vooctxtrec
                {hitBot = fn t => (t,nextRedNum),
                 hitDom = fn _ => fn b => fn t => fn _ => (b::t,nextRedNum),
                 hitVoo = fn (id,D) => fn b => fn _ => fn rect =>
                        ((if member id redWhich
                          then folder gluon (narrow (hd
                                             (proformas redProb  "o" D)))
                                      innerProfs
                          else raise noReds)
                          handle noReds => ((cons b)**iota)) (rect ())}
                redPref
        in  on (doneReds,Prop) [domvoo redId, MrFreeze UnFroz]
        end
        handle noReds => on modProb [domvoo redId, MrFreeze UnFroz])

fun mess (s:string) =
    if (!clobberDiag) then ((print s);(flush_out std_out)) else ()

in

fun holyClobber strat elimNames PHide elimRule (subgoal,target,whereReds)
    problem =
    let val _ = mess "clob "

        (* get preliminary reduction info *)
        val redInfo = getRedInfo (#1 (parseApp elimRule))
                                 (problem,whereReds,subgoal)

        (* NOTE We must be careful not to do any side effects to
           the problem until after we've attempted argument synthesis.
           Tactics must be allowed to use Clobber and fail harmlessly
           at this point. *)

        (* find the subgoal, parse the elim rule *)
        val elimType = type_of_constr elimRule
        val probSub = voodom subgoal problem
        val (elimPref,elimTail) = parselim probSub elimNames elimType
                                  handle _ =>
                                  ((domvoo subgoal probSub); (* careful now *)
                                   (raise noClobber))
        val problem = domvoo subgoal probSub
        val {P,PHI,SUBGOAL,Y,PRED,ITER,A,H,EQN} = elimNames

        (* make solution frame, spot targetter *)
        val (elimAA,elimVV) = ArgsAndVis iota elimPref
        val specimen = MkApp ((elimRule,elimAA),elimVV)
        val (solPref,targetter) = vooctxtrec
            {hitBot = fn _ => ([],b42),
             hitDom = fn _ => failwith "clobber disaster",
             hitVoo = fn (id as (s,i),_) => fn b => fn _ => fn rect =>
                      let fun zob jd = if member s [Y,P] then id
                                       else jd
                      in  ((cons (pihole b))**zob)
                          (rect ())
                      end} elimPref
        val clob2R = ((Let,Def),"",specimen,elimTail):!
                     (Voo (("clobber",2),([],specimen)))
        val solFrame = voodom ("clobber",2)
                       (clob2R::solPref,Prop)
        val _ = if targetter = b42 then raise noClobber else ()
        val _ = mess "frame "
        val (holesLeft,_) = on solFrame
            [vooSolve true targetter ([],target), (* don't check now *)
             voosynth, (* synth fixes any type prob caused by vooSolve true *)
             domvoo ("clobber",2)]
            handle _ => raise noClobber
        val _ = mess "synth "

        val (probPref,probTail) =
            on problem [vooattack subgoal ("clobber",1),
                        vooIntroTac ("clobber",1)]
        val afterInfer = ((hd probPref)::(holesLeft@(tl probPref)),probTail)

        val _ = if (!clobberDebug)
                then ((print "Clobber infers arguments:\n");
                      (vooprintstate afterInfer))
                else ()

        val stratProb as (stratPref,stratTail) = afterInfer
        (* fix everything on which types of holes depend *)
        val (tailFn,tailArgs,tailVis) =
            parseApp (type_of_constr (vid stratProb ("clobber",2)))
        val ldaVars = vooctxtrec
           {hitBot = fn _ => [],
            hitDom = fn _ => fn _ => fn _ => fn _ => [],
            hitVoo = fn _ => fn b => fn _ => fn rect =>
                    (if (ref_bind b)=Lda then cons b else iota)
                    (rect ())} stratPref
        val PhiSubgTypes = vooctxtrec
           {hitBot = fn _ => [],
            hitDom = fn _ => fn _ => fn _ => fn _ => [],
            hitVoo = fn ((s,_),_) => fn b => fn _ => fn rect =>
                    (if (#1 (ref_bd b))=HoleBV andalso (s=PHI orelse s=SUBGOAL)
                     then cons (ref_typ b) else iota)
                    (rect ())} stratPref
        val (genova,remaining) = vooctxtdepfilter ldaVars PhiSubgTypes
        val genova = map bid genova
        val (indexVars,remaining) = vooctxtdepfilter remaining tailArgs
        val indVarIds = map bid indexVars
        val relevant = vooctxtrec
           {hitBot = fn _ => indVarIds,
            hitDom = fn _ => fn _ => fn _ => fn _ => indVarIds,
            hitVoo = fn _ => fn b => fn _ => fn rect =>
                     let val l = rect ()
                         val d = voodep1l (ref_typ b)
                     in  if joint l d then (bid b)::l else l
                     end} ldaVars
        val backEnd = stratProb ?! ("clobber",1)
        val (tailVars,_) = vooctxtdepfilter remaining [$!backEnd]
        val critical = vooctxtrec
           {hitBot = fn _ => indVarIds,
            hitDom = fn _ => fn _ => fn _ => fn _ => indVarIds,
            hitVoo = fn _ => fn b => fn _ => fn rect =>
                     let val l = rect ()
                         val d = voodep1l (ref_typ b)
                     in  if joint l d then (bid b)::l else l
                     end} tailVars
        val targIdOp = SOME (tid target) handle missing_voodoo => NONE
            (* must never gen over the target, nor must it be a pi
               unless it's relevant *)
        fun okPi id = not ((member id genova) orelse ((SOME id)=targIdOp))
        val theStratTest = (* tests to see if sth should be a pi in Phi *)
            case strat
              of MaximalStrat => const (fn id => not (member id genova))
               | MiddleStrat  => const (fn id => member id relevant)
               | MinimalStrat => const (fn id => member id critical)
               | MissingStrat l => const (fn id => ((member id relevant)
                                             orelse (okPi id))
                                             andalso (not (member id l)))
               | RightStrat => (fn [] => (fn id => member id relevant)
                                 | _ => (fn id =>  not (member id genova)))
        val (genPre,redPre) = vooctxtrec
            {hitBot = fn _ => ([],[]),
             hitDom = fn _ => fn b => fn t => fn _ => ([],[]),
             hitVoo = fn (id,_) => fn b => fn _ => fn rect =>
                      let val (gp,rp) = rect ()
                          val bo = ref_bind b
                      in  if bo=Let orelse bo=Hole
                          then (gp,rp)
                          else if theStratTest rp id
                          then (gp,b::rp)
                          else if targIdOp=(SOME id)
                          then (gp,rp)
                          else (b::gp,rp)
                      end}
            probPref

        val (redPref,(zapR,pazR)) = copyCtxt pify redPre
        val (genPref,(zapG,pazG)) = copyCtxt pify genPre

        val tailArgs = map (fn t => zapR%>>t) tailArgs

        (* now we switch our attention to building Phi *)
        (* build Phi with no equations *)
        val Phid = tid tailFn
                   handle missing_voodoo => failwith "Can't Clobber!"
        fun Thud () = failwith "bug in Clobber"
        val backEnd = stratProb ?! ("clobber",1)
        val PhiNoEqs = on stratProb
                       [vooattack Phid ("phi",1),
                        vooIntroTac ("phi",1),
                        fn (h::t,T) => (h::(redPref@t),T) | _ => Thud (),
                        ("phi",1) \ (zapR%>>>backEnd)]

        val _ = mess "fix "
        val _ = if (!clobberDebug)
                then ((print "Clobber ready to compute Phi:\n");
                      (vooprintstate PhiNoEqs))
                else ()

        (* build the reduced equations; spot the affected goal args *)
        val (Eq,_) = Require ["Eq"]
        type buildInfo = {S : binding list * cnstr,
                          args : cnstr list,
                          triLdas : binding list,
                          qi : int,
                          dep : int,
                          sArg : cnstr list, sVis : prntVisSort list}

        val baseQi = safeNumber PhiNoEqs EQN 1
        fun checkFetch (C,_) id = vooctxtrec
           {hitBot = voobottom,
            hitDom = fn _ => fn _ => fn _ => fn _ => raise missing_voodoo,
            hitVoo = fn (jd,_) => fn b => fn t => fn rect =>
                     if id=jd
                     then if (ref_bind b)<>Pi then raise missing_voodoo
                          else vooctxtrec
                              {hitBot = fn _ => b,
                               hitDom = fn _ => fn _ => fn _ => fn _ => b,
                               hitVoo = fn _ => fn x => fn _ => fn rect =>
                                        case ref_bind x
                                          of Pi => rect ()
                                           | Lda => b
                                           | _ => raise missing_voodoo} t
                     else rect ()} C
        val PhiStuff = vooctxtrec
            {hitBot = voobottom,
             hitDom = fn _ => fn _ => fn _ => fn _ => fn _ => fn _ =>
                      {S = PhiNoEqs, args = tailArgs,
                       triLdas = [], qi = baseQi, dep = 0,
                       sArg = [], sVis = []},
             hitVoo = fn (id,_) => fn b => fn _ => fn rect =>
                      fn ldas => fn oc =>
                      case ref_bind b
                        of Pi => rect () [] (union (voodep1l (ref_typ b)) oc)
                         | Sig => rect () [] (union (voodep1l (ref_typ b)) oc)
                         | Lda => (*...
......................................:
:...*)let val bInfo : buildInfo as {S,args,triLdas,qi,dep,sArg,sVis} =
              rect () (b::ldas) (union (voodep1l (ref_typ b)) oc)
          val (tc,tt) = bCT b (* get these after doing rect: side-fx *)
          val bigB = $!(vooetastate (tc@triLdas,tt))
          val lhs =
              if dep=0 then Ref b
              else let val (sOp,_) = Require ["dep","subst",string_of_num dep]
                   in  App ((sOp,sArg@[bigB,Ref b]),sVis)
                   end                (* last 2 vis already there *)
          val (ah,at) = case args of (h::t) => (zapR%>>h,t) | _ => Thud ()
      in (let val rhid = tid ah
              val rhb = checkFetch S rhid (* possible coalescence ? *)
              val ((_,v),_,dom,ran) = ref_bd b
              val _ = if member rhid oc (* does the var get used? *)
                      then case par_unif [] dom (type_of_constr lhs)
                             of NONE => raise missing_voodoo (* no go *)
                              | SOME _ => () (* hopefully ok to coerce *)
                      else () (* not used, so who cares ?*)
              val _ = if bmem rhb (#1 (vooctxtdepfilter (#1 S) [lhs]))
                      then raise missing_voodoo else ()

              val _ = (b<:((Lda,v),ref_nam rhb,dom,ran))<!(Voo (rhid,(tc,tt)))
          in  {S=vooSolve true rhid ([],lhs) S,
               args=map (fn t => [(rhb,lhs)]%>>t) at,triLdas=triLdas,
               qi=qi,dep=dep,sArg=sArg,sVis=sVis}
          end
          handle missing_voodoo =>
          let val theEqn =
                  App ((Eq,[type_of_constr ah,lhs,ah]),
                           [NoShow,      ShowNorm,ShowNorm])
              val qb = ((Pi,Vis),"eqn",theEqn,type_of_constr theEqn):!
                       (Voo ((EQN,qi),([],theEqn)))
              val S' = vooshove qb S
          in  if dep=0
              then if voobin b (ldas,Prop)
              then (* need to start triangling *)
              {S=S',args=at,triLdas=[b],qi=qi+1,dep=1,
               sArg=[bigB,   Ref b,  ah,   Ref qb], (* last 2 vis *)
               sVis=[NoShow,NoShow,NoShow,ShowNorm,ShowNorm,ShowNorm]}
              else (* no need to triangle *)
              {S=S',args=at,triLdas=[],qi=qi+1,dep=0,sArg=[],sVis=[]}
              else (* carry on triangling *)
              {S=S',args=at,triLdas=b::triLdas,qi=qi+1,dep=dep+1,
               sArg=sArg@[bigB,   Ref b,   ah,    Ref qb],
               sVis=     NoShow::NoShow::NoShow::ShowNorm::sVis} (* symmetry *)
          end)
      end (*....................*)
                         | _ => Thud ()} (#1 PhiNoEqs) [] []
        val PhiEqsBuilt = vooetastate (#S PhiStuff)
        val Eq_refl = ?"%Eq refl%"       (* now build solutions for extra *)
        val (phiAA,phiVV,_,_) = vooctxtrec (* pis in Phi                  *)
            {hitBot = const ([],[],[],tailArgs),
             hitDom = fn _ => fn _ => fn _ => fn _ => ([],[],[],tailArgs),
             hitVoo = fn (id as (s,i),_) => fn b => fn _ => fn rect =>
                      let val (aa,vv,zz,gg) = rect ()
                      in
                      case ref_bd b
                        of ((Pi,v),_,dom,_) =>
                           let val a = if s=EQN andalso i>=baseQi
                                       then case dom
                                              of App ((_,[_,_,rhs]),_) =>
                                                 let val rhs' =
                                                     pazR%>>(zz%>>rhs)
                                                 in
                                                 App ((Eq_refl,
                                                  [type_of_constr rhs',rhs']),
                                                     [NoShow,ShowNorm])
                                                 end
                                                   | _ => Thud ()
                                       else zz%>>(pazR%>>(Ref b))
                           in (aa@[a],vv@[prVis v],zz,gg)
                           end
                         | ((Sig,_),_,_,_) => (aa,vv,zz,gg)
                         | ((Lda,_),_,_,_) => (aa,vv,(b,hd gg)::zz,tl gg)
                         | _ => rect ()
                      end} (#1 PhiEqsBuilt)

        val PhiEqsBuilt = domvoo Phid PhiEqsBuilt

        val Phib = fetch PhiEqsBuilt Phid
        val PhiV = $!(bCT Phib)
        val Phib = case ref_bd Phib
                     of (bv,nam,_,ty) => Phib<:(bv,nam,PhiV,ty)

        val _ = mess "phi "
        val _ = if (!clobberDebug)
                then ((print "Clobber computes Phi:\n");
                      (vooprintstate PhiEqsBuilt))
                else ()

        val GoalSolved = on PhiEqsBuilt
                         [if PHide then voosubdef Phid else iota,
                          ("clobber",1)\([],MkApp ((Ref clob2R,phiAA),phiVV)),
                          voosubdef ("clobber",2)]

        val _ = if (!clobberDebug)
                then ((print "Clobber solves for Phi:\n");
                      (vooprintstate GoalSolved))
                else ()

        val _ = mess "gen "
        (* now generalise the spare Phis *)
        val (genArgs,genVis) = ArgsAndVis (fn t => pazG%>>t) genPref
        val (newPhis,PhisGone) = vooctxtrec
            {hitBot = fn _ => ([],GoalSolved),
             hitDom = fn _ => fn b => fn t => fn _ => ([],GoalSolved),
             hitVoo = fn (id,(dc,dt)) => fn b => fn _ => fn rect =>
                      if (#1 id)=PHI andalso (#1 (ref_bd b))=HoleBV
                      then
                      let val genPhi = vooCopy (dc@genPref,dt)
                          val b' = noo (HoleBV,ref_nam b) id genPhi
                          val soln = MkApp ((Ref b',genArgs),genVis)
                      in  ((cons b')**(id \ ([],soln))) (rect ())
                      end
                      else if (#1 id)=PHI andalso (#1 (ref_bd b))=(Let,Def)
                      then
                      let val (gpls,(gplz,_)) = copyCtxt ldify genPref
                          val (dc,dt) = gplz%>>>(zapG%>>>(dc,dt))
                          val genPhi = (dc@gpls,dt)
                          val b' = noo ((Let,Def),ref_nam b) id genPhi
                          val soln = MkApp ((Ref b',genArgs),genVis)
                      in  ((cons b')**(id \ ([],soln))) (rect ())
                      end
                      else if (ref_bind b)=Lda then ([],GoalSolved)
                      else rect ()} (#1 GoalSolved)

        (* now fiddle with the subgoals *)
        fun fiddleSubg (id,(dc,dt)) b (l,S) =
            let val newSubgPref = (map (alBind zapG) dc)@genPref
                val theSg = vooCopy (newSubgPref,zapG%>>dt)
                val b' = noo (HoleBV,ref_nam b) id theSg
             in  ((b'::l),(id \ ([],MkApp ((Ref b',genArgs),genVis))) S)
            end


        val (newSubgs,bitsGone) =
            vooctxtrec
            {hitBot = fn _ => ([],PhisGone),
             hitDom = fn _ => fn b => fn t => fn _ => ([],PhisGone),
             hitVoo = fn v as ((s,_),_) => fn b => fn _ => fn rect =>
                      (if s=SUBGOAL then fiddleSubg v b else iota) (rect ())}
            (#1 PhisGone)

        val (newSubgs,_) = (if SUBGOAL=(#1 subgoal) andalso newSubgs<>[]
                            then vooRename [(bid (hd newSubgs),subgoal)]
                            else iota) (newSubgs,Prop)

        val newBits = newSubgs@newPhis

        (* solve the goal in terms of the bits *)
        val (clobPref,clobTail) = vooetastate bitsGone
        val readyProb = (vooctxtrec
             {hitBot = fn l => newBits@l,
              hitDom = fn _ => fn b => fn t => fn _ => b::(newBits@t),
              hitVoo = fn _ => fn b => fn _ => fn rect => b::(rect())}
             clobPref,clobTail)
        val solvedProb = vookcatta subgoal readyProb

        val _ = if (!clobberDebug)
                then ((print "Clobber solves goal:\n");
                      (vooprintstate solvedProb))
                else ()

        val reddedProb =
            case redInfo
              of NONE => solvedProb
               | SOME stuff =>
                 let val _ = "red "
                     val thang = narrowReds solvedProb stuff
                     val _ = if (!clobberDebug)
                             then ((print "Clobber refines reductions:\n");
                                   (vooprintstate thang))
                             else ()
                 in  thang
                 end
        val _ = mess "done\n"

    in  (newSubgs,reddedProb)
end

fun Clobber strat elimNames elimRule stuff problem =
    #2 (holyClobber strat elimNames true elimRule stuff problem)

end

fun pick S sid tid =
    let val S' = S ?! sid
    in  vid S' tid
    end

fun Elim strat rule (sg::targ::what) S =
    let val targ = pick S sg targ
    in  Clobber strat usualElimNames rule
                (sg,targ,case what of [] => NONE
                                    | (h::_) => SOME h) S
    end
  | Elim _ _ _ _ = failwith "bad Elim"

fun vps S = ((vooprintstate S);S)


(*************************************************************************)

open Quartermaster


fun legoNames names =
  let val theGoal = #2 (Synt.goaln (~9999))
      fun newName v "" n d r = Bind ((Pi,v),n,d,r)
        | newName v "#" n d r = failwith "Names: # for Pi"
        | newName v x _ d r = Bind ((Pi,v),x,d,r)
      fun doNaming [] g = g
        | doNaming (x::xs) (Bind ((Pi,v),n,d,r)) =
            newName v x n d (doNaming xs r)
        | doNaming _ (Bind _) = failwith "Names: ran out of Pi's"
        | doNaming xs t = case whnf t
                            of Bind b => doNaming xs (Bind b)
                             | _ => failwith "Names: ran out of Pi's"
      val newGoal = doNaming names theGoal
  in (Namespace.Equiv [] newGoal; message"Names"; Toplevel.Pr())
  end

fun legoAbstract xid quid term =
  let val (C,T) = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
               [voodom ("goal",1),
                introall whnf "prem" 1
               ]
      val (C',(zap,paz)) = copyCtxt iota C
      val (otm,oty) = fEvalCxt C term
      val tm = zap %>> otm
      val ty = zap %>> oty
      val T' = zap %>> T
      val xb = noo ((Pi,Vis),xid) ("ab",1) ([],ty)
      fun myRew _ t = if par_tm t tm then Mod (Ref xb) else UMod
      val (DC,DT) = vooshove xb (myRew >>> (C',T'))
      val paz = (xb,otm)::paz
      val ((DC,DT),paz) = case quid
           of "" => ((DC,DT),paz)
            | _ => let val JM = Supply ["JM"]
                       val JMr = Supply ["JM","refl"]
                       val qb = noo ((Pi,Vis),quid) ("abq",1)
                                    ([],MkApp ((JM,[ty,ty,Ref xb,tm]),
                                         [NoShow,NoShow,ShowNorm,ShowNorm]))
                   in  (vooshove qb (DC,DT),
                        (qb,MkApp ((JMr,[oty,otm]),[NoShow,ShowNorm])
                         )::paz)
                   end
      val (aa,vv) = ArgsAndVis (fn t => paz %>> t) DC
      val subg = noo (HoleBV,"") ("paf",1) (DC,DT)
      val S = on (C,T) [
           domvoo ("goal",1),
           vooattack ("goal",1) ("bof",1),
           vooIntroTac ("bof",1),
           vooBeforeDom subg,
           ("bof",1) \ ([],MkApp ((Ref subg,aa),vv)),
           vooetastate,
           vookcatta ("goal",1)
          ]
  in  vooLegoRefine [("type",1),("blah",1)] S
  end

fun legoDelete id =
  let val (C,T) = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
               [voodom ("goal",1),
                introall whnf "prem" 1
               ]
      val (C',(zap,paz)) = copyCtxt iota C
      val (_,C') = filter (fn b => (ref_nam b) = id) C'
      val T' = zap %>> T
      val (aa,vv) = ArgsAndVis (fn t => paz %>> t) C'
      val subg = noo (HoleBV,"") ("paf",1) (C',T')
      val S = on (C,T) [
           domvoo ("goal",1),
           vooattack ("goal",1) ("bof",1),
           vooIntroTac ("bof",1),
           vooBeforeDom subg,
           ("bof",1) \ ([],MkApp ((Ref subg,aa),vv)),
           vooetastate,
           vookcatta ("goal",1)
          ]
  in  vooLegoRefine [("type",1),("blah",1)] S
  end


fun TTU x y =
    let val xt = type_of_constr x
        val yt = type_of_constr y
    in  case par_unif [] xt yt
          of SOME s => par_unif s x y
           | NONE => NONE
    end

fun outerClaim bs (C,T) = (vooctxtrec {
      hitBot = fn _ => bs,
      hitDom = fn _ => fn b => fn rs => fn _ => b::(bs@rs),
      hitVoo = fn _ => fn b => fn _ => fn rect => b::(rect ())
    } C,T)

fun octElim g rv ts S =
    let val Target = unRef (Supply ["Target"])
        val TargetOn = unRef (Supply ["Target","on"])
        val JMQ = Supply ["JM"]
        val JMr = Supply ["JM","refl"]
        fun makeElim e (b::C,T) =
            (b::
             (noo ((Let,Def),"elim") e ([],rv))::C,T)
          | makeElim _ _ = failwith "disaster"
        fun tryTarget t C =
            vooctxtrec {
            hitBot = fn _ => NONE,
            hitDom = fn _ => fn _ => fn _ => fn _ => NONE,
            hitVoo = fn ((s,j),_) => fn b => fn _ => fn rect =>
                     case rect ()
                       of SOME s => SOME s
                        | NONE => if s = "arg"
                          then case ref_typ b
                                 of App ((Ref tb,[tt,tv]),_) =>
                                    if sameRef tb Target
                                    then case TTU t (Ref b)
                                           of SOME s => SOME s
                                            | _ => failwith "bad target"
                                    else NONE
                                  | _ => NONE
                          else NONE
            } C
        fun tryAnything t C =
            vooctxtrec {
            hitBot = fn _ => NONE,
            hitDom = fn _ => fn _ => fn _ => fn _ => NONE,
            hitVoo = fn ((s,j),_) => fn b => fn _ => fn rect =>
                     case rect ()
                       of SOME s => SOME s
                        | NONE => if s = "arg"
                          then TTU t (Ref b)
                          else NONE
            } C
        fun target ts i (b::e::C,T) =
            let val (ehs,etip) = introall whnf "arg" i
                                 ([],ref_typ e)
                val (aa,vv) = ArgsAndVis iota ehs
                val ehs = map safepihole ehs
                val i' = case ehs
                           of [] => 1
                            | (e::_) => 1+(#2 (bid e))
                val e' = noo ((Let,Def),"elim") (bid e)
                             ([],MkApp ((ref_val e,aa),vv))
                val C' = ehs@C
            in  case ts
                  of [] => (b::e'::C',T)
                   | (t::ts) =>
               (case tryTarget (App ((Ref TargetOn,[type_of_constr t,t]),
                                                   [NoShow,ShowNorm])) C'
                  of SOME s => target ts i' (s $>>> (b::e'::C',T))
                   | NONE =>
                (case tryAnything t C'
                   of SOME s => target ts i' (s $>>> (b::e'::C',T))
                    | NONE => failwith "it doesn't eliminate that"
               ))
            end
          | target _ _ _ = failwith "disaster"
        fun motive (S as (_::e::_,_)) =
            let val (Phi,PhiAA,PhiVV) = parseApp (ref_typ e)
                val Phi = unRef Phi
                val S = case bid Phi
                          of ("arg",j) => vooRename [(("arg",j),("Phi",1))] S
                           | _ => failwith "no motive variable"
                val _ = if voofold false (fn a => fn b => a orelse b)
                           (fn b => holy b andalso (#1 (bid b)) = "arg")
                           (CnLst PhiAA)
                        then failwith "not fully targetted"
                        else ()
                val (b,e) = case S
                              of (b::e::_,_) => (b,e)
                               | _ => failwith "disaster"
                val holeTypes = CnLst (Cfoldr
                                (fn b => if holy b andalso
                                            (#1 (bid b)) = "arg"
                                         then cons (ref_typ b)
                                         else iota)
                                [] (fst S))
                fun parametric b = depends b holeTypes
                val embryo = ref_val e
                fun irrelevant b = depends b embryo
                                   andalso (not (depends b (CnLst PhiAA)))
                val (C,T) = voodom ("Phi",1) S
                val (Inds,T) = introall whnf "ind" 1 ([],T)
                val S = on (Inds@C,T) [
                        domvoo ("Phi",1),
                        vooattack ("Phi",1) ("Ford",1),
                        vooIntroTac ("Ford",1)
                        ]
                val large = case type_of_constr (#2 S)
                              of Prop => (fn _ => false)
                               | u => (fn b => not 
                                  (par_tm (type_of_constr (ref_typ b)) u))
                fun unhelpful b = parametric b orelse
                                  large b
                val (C,T) = domvoo ("Phi",1) S
                val goalTip = type_of_constr T
                val (fixPrems,varyPrems) = vooctxtrec {
                      hitBot = fn _ => fn _ => ([],[]),
                      hitDom = fn _ => fn _ => fn _ => fn _ => fn _ => ([],[]),
                      hitVoo = fn ((s,j),_) => fn b => fn _ => fn rect =>
                               fn (fts,ts) => let val t = ref_typ b in
                        if (ref_bind b) = Lda
                        then if unhelpful b orelse depends b (CnLst fts)
                             then ((cons b) ** iota)
                                  (rect () (t :: fts,t :: ts))
                             else if irrelevant b
                                     andalso (not (depends b (CnLst ts)))
                                  then rect () (fts,ts)
                                  else (iota ** (cons b))
                                       (rect () (fts,t :: ts))
                        else rect () (fts,ts)
                        end
                    } C ([],[goalTip])
                val (C,T) = voodom ("Phi",1) (C,T)
                val (varyCopy,(vzap,vpaz)) =
                      copyCtxt ((vNam "vary") o pify) varyPrems
                val (Lefts,_) = ArgsAndVis iota Inds
                val Rights = map (fn t => vzap %>> t) PhiAA
                fun bdel b [] = NONE
                  | bdel b (b'::bs) = if sameRef b b' then SOME bs
                                      else case bdel b bs
                                             of SOME bs => SOME (b'::bs)
                                              | NONE => NONE
                fun mkq i l r = noo ((Pi,Vis),"") ("eqn",i)
                    ([],App ((JMQ,[type_of_constr l,type_of_constr r,l,r]),
                             [NoShow,NoShow,ShowNorm,ShowNorm]))
                fun qs ((l as (Ref lb))::ls) (r::rs) i vs es zz =
                   (case zz %>> r
                      of Ref rb =>
                        (case bdel rb vs
                           of SOME vs' =>
                              let val lt = ref_typ lb
                                  val rt = zz %>> (ref_typ rb)
                              in  if par_tm lt rt
                                  then qs ls rs (i+1) vs' es ((rb,Ref lb)::zz)
                                  else qs ls rs (i+1) vs
                                          ((mkq i l (Ref rb))::es) zz
                              end
                            | NONE => (**************
                              if not (exists (sameRef rb) Inds)
                                 andalso par_tm (ref_typ lb) (ref_typ rb)
                              then qs ls rs (i+1) vs
                                      ((mkq i l (Ref rb))::es)
                                      ((rb,Ref lb)::zz)
                              else **************)
                                   qs ls rs (i+1) vs
                                         ((mkq i l (Ref rb))::es) zz)
                       | r => qs ls rs (i+1) vs ((mkq i l r)::es) zz)
                  | qs _ _ _ vs es zz = (vs,es,zz)
                val (vs,es,zz) = qs Lefts Rights 1 varyCopy [] []
                val (FC,FT) = zz %>>> (es@vs,vzap %>> goalTip)
                val (aa,vv) = vooctxtrec {
                     hitBot = fn _ => iota,
                     hitDom = fn _ => fn _ => fn _ => fn _ => iota,
                     hitVoo = fn ((s,j),_) => fn b => fn _ => fn rect =>
                              fn (aa,vv) =>
                             (case (ref_bind b,s)
                                of (Lda,_) => (aa,vv)
                                 | (Pi,"vary") => rect ()
                                    ((vpaz %>> (Ref b))::aa,
                                     (prVis (ref_vis b))::vv)
                                 | (Pi,"eqn") => 
                                   let val tm = nth PhiAA j
                                       val rfl = 
                                         App ((JMr,[type_of_constr tm,tm]),
                                                   [NoShow,ShowNorm])
                                   in rect () (rfl::aa,ShowNorm::vv)
                                   end
                                 | _ => failwith "poison is queen"
                             )
                    } FC ([],[])
                val (C,T) = on (FC@(tl C),FT) [
                             vooetastate,
                             vookcatta ("Phi",1),
                             fn S => vooSolve false ("bof",1) ([],
                                     MkApp ((vid S ("elim",1),aa),vv)) S,
                             voosubdef ("elim",1)
                            ]
                val (fixAA,fixVV) = ArgsAndVis iota fixPrems
                val (subgs,sols) = vooctxtrec {
                  hitBot = const ([],[]),
                  hitDom = fn _ => fn _ => fn _ => fn _ => ([],[]),
                  hitVoo = fn ((s,j),D) => fn b => fn _ => fn rect =>
                          (case s
                             of "arg" =>
                                let val (pis,(pzap,ppaz)) =
                                       copyCtxt pify fixPrems
                                    val (DC,DT) = pzap %>>> D
                                    val gb = noo (HoleBV,ref_nam b)
                                                 ("subgoal",j)
                                                 (DC@pis,DT)
                                in  (cons gb) **
                                    (cons ((s,j),
                                           ([],MkApp ((Ref gb,fixAA),fixVV))))
                                end
                              | _ => iota
                          ) (rect ())
                } C
            in  on (C,T) [
                 outerClaim subgs,
                 fn S => foldr (op\) S sols,
                 vooetastate
                ]
            end
          | motive _ = failwith "disaster"
        val S = on S [
                 vooattack g ("bof",1),
                 vooIntroTac ("bof",1),
                 makeElim ("elim",1),
                 target ts 1,
                 motive,
                 vookcatta g
                ]
    in  S
    end

fun legoOctElim (elim:cnstr_c) =
  let val S = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
              [voodom ("goal",1),
               introall whnf "prem" 1
              ]
      val (C,_) = S
      fun unpack (App_c (_,f,t)) ts = unpack f (t::ts)
        | unpack r ts = (r,ts)
      val (r,ts) = unpack elim []
      val rv = #1 (fEvalCxt C r)
      val ts = map ((#1) o (fEvalCxt C)) ts
      val _ = legoprint rv
      val _ = map legoprint ts
      val S = on S
              [domvoo ("goal",1),
               octElim ("goal",1) rv ts,
               vps
              ]
  in  vooLegoRefine [("type",1),("blah",1)] S
  end
;

(*ConorTools.OctElim := legoOctElim;*)

exception badElim

fun analyseElim T =
   (let val (EC,ET) = introall iota "z" 1 ([],T)
        val Tgb = unRef (Supply ["Target"])
        val (tgs,rest) = filter
                         (fn b => (case parseApp (ref_typ b)
                                     of (Ref b',_,_) => sameRef Tgb b'
                                      | _ => false)) EC
        val (AXC,MB) = vooDepCut rest (map ref_typ tgs)
        val (A,XC) = vooDepCut AXC (map ref_typ MB)
        val (X,C) = vooDepCut XC [ET]
        val (M,B) = vooDepCut MB [ET]
        val (Phi,pp,vv) = parseApp ET
        val phib = unRef Phi
        val _ = case M
                  of [b] => if sameRef b phib then () else raise badElim
                   | _ => raise badElim
        val _ = case vooDepCut MB pp
                  of ([],_) => ()
                   | _ => raise badElim
        val (F,G) = filter (isTypeFam o ref_typ) B
        fun renamer ((s,i),C) rs = fst
             (Cfoldr (fn b => fn (rs,i) => ((bid b,(s,i))::rs,i+1)) (rs,i) C)
        val R = (bid phib,("Phi",1))::(foldr renamer []
                [(("tg",1),tgs),(("a",1),A),(("x",1),X),(("c",1),C),
                 (("F",1),F),(("g",1),G)])
        val (EC,ET) = on (vooRename R (EC,ET)) [
              voodom ("Phi",1),
              introall iota "i" 1,
              domvoo ("Phi",1)
            ]
        fun XHify (C,T) =
            let val (CX,CH) = Cfoldr
                              (fn b => fn (CX,CH) =>
                               if depends phib (ref_typ b) then (CX,b::CH)
                                                           else (b::CX,CH))
                              ([],[]) C
            in  vooRename (foldr renamer [] [(("x",1),CX),(("h",1),CH)]) (C,T)
            end
        fun gnobble g S = on S [
            voodom g,
            introall iota "z" 1,
            XHify,
            domvoo g
          ]
        val (EC,ET) = foldr (gnobble o bid) (EC,ET) G
        val ind = exists ((exists (hasName "h")) o fst o bCT) G
    in ((EC,ET),ind)
    end handle _ => raise badElim)

