(***********************************************************************)
(********                                                       ********)
(********        gluing elim rules together                     ********)
(********                                                       ********)
(***********************************************************************)

(* glueElim takes an outer elim rule and an inner elim rule (with
   distinct parse name systems), also a choice of outer subgoal and
   premise within that subgoal; this premise is then eliminated
   using the inner rule and the resulting theorem is rearranged
   via a tupling trick to have stronger inductive hypotheses
   for funkier structural recursion *)

val usualInnerNames = {P="q",PHI="Psi",SUBGOAL="subsub",Y="z",PRED="prpr",
                       ITER="itit",A="b",H="g",EQN="eqeq"}

fun vooTupleTac (bInit,bUpd,bTest) id S =
    let val (C,T) = S ?! id
        val (ldas,(zap,_)) = copyCtxt ldify C
        val (C',bag) = vooctxtrec
            {hitBot = fn b => (b,bInit),
             hitDom = fn _ => fn b => fn _ => fn rect =>
                      ((cons b)**iota) (rect ()),
             hitVoo = fn _ => fn b => fn _ => fn rect =>
                      let val (c,bag) = rect ()
                      in ((if bTest b bag then sigify b else b)::c,bUpd b bag)
                      end} C
        val newSubg = noo (HoleBV,"") id (C',T)
        val trickT = vooctxtrec
           {hitBot = fn _ => Ref newSubg,
            hitDom = fn _ => fn _ => fn _ => fn _ => Ref newSubg,
            hitVoo = fn _ => fn b => fn _ => fn rect =>
                     case ref_bind b
                       of Pi => MkApp ((rect (),[zap%>>(Ref b)]),
                                       [prVis (ref_vis b)])
                        | Sig => Proj (Snd,rect ())
                        | _ => failwith "can't do tuple trick"} C'
        val trick = vooetastate (ldas@[newSubg],trickT)
    in  (id \ trick) S
    end


fun glueElim (outerNames:elimComponentNames) outerRule
             subg prem
             (innerNames:elimComponentNames) innerRule =
    let (* phase 1
           establishing bona fides *)

        val outerType = type_of_constr outerRule
        val outerParse = parselim ([],Prop) outerNames outerType
        val {P=oP,PHI=oPHI,SUBGOAL=oSUBGOAL,Y=oY,PRED=oPRED,ITER=oITER,
             A=oA,H=oH,EQN=oEQN} = outerNames

        val innerType = type_of_constr innerRule
        val innerParse = parselim ([],Prop) innerNames innerType
        val {P=iP,PHI=iPHI,SUBGOAL=iSUBGOAL,Y=iY,PRED=iPRED,ITER=iITER,
             A=iA,H=iH,EQN=iEQN} = innerNames

        val (outerC,outerT) = vooCopy outerParse
        val (oAA,oVV) = ArgsAndVis iota outerC
        val subgB = pihole (fetch (outerC,Prop) subg)
        val pfCtxt = vooctxtrec
           {hitBot = fn b => fn _ => [], hitDom = voocontinue,
            hitVoo = fn (id as (s,_),_) => fn b => fn _ => fn rect => fn f =>
                     if s=oSUBGOAL
                     then if id=subg
                          then if f then rect () true
                               else subgB::(rect () true)
                          else if f then (pihole b)::(rect () true)
                               else subgB::(pihole b)::(rect () true)
                     else (pihole b)::(rect () f)} outerC false
        val pfTail = MkApp ((outerRule,oAA),oVV)
        val WORK = (pfCtxt,pfTail)

        val subgS = WORK ?! subg
        val premB = fetch subgS prem
        fun tupTest b _ = (#1 (bid b))=oITER andalso depends premB (ref_typ b)
        fun hitSub i S = on S
            [KJunifyTestMore (const true) (iSUBGOAL,i),
             vooSubSubSequence (iSUBGOAL,i) iITER simplifyPremise,
             fn S => prologSubHoles (cnstr_size (#2 (S?!(iSUBGOAL,i))))
                     [fetch S (iSUBGOAL,i)] S]
        fun spliceSubgs (S as (C,T)) =
            let val (subgs,others) =
                    filter (fn b => member (#1 (bid b)) [iSUBGOAL,oSUBGOAL]) C
            in  foldr vooshove (others,T) subgs
            end
        val THM = on WORK
                   [vooTupleTac ((),const (const ()),tupTest) subg,
                    Clobber MaximalStrat innerNames innerRule
                              (subg,Ref premB,NONE),
                    vooSubSequence iSUBGOAL hitSub,
                    (map holeldav)**iota,
                    spliceSubgs]
        val thm = $!THM
    in  (thm,type_of_constr thm)
    end

