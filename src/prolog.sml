(**************************************************************)
(*********                                            *********)
(*********           tactique prolog                  *********)
(*********                                            *********)
(**************************************************************)

(* actually, this isn't really prolog 'cos it doesn't backtrack,
   but it could be made to *)

exception Prolog

val holeName = "hole"
val holeNum = ref 0

fun nextHole () = ((holeNum := (!holeNum)+1);(holeName,!holeNum))

fun usualGuesser holes tm v dom ran =
    let val nh = noo (HoleBV,"") (nextHole ()) ([],dom)
        val guess = Ref nh
        val ran = subst1 guess ran
        val tm = MkApp ((tm,[guess]),[prVis v])
    in (nh::holes,tm,ran)
    end

fun reflGuesser holes tm v dom ran =
    let val (f,aa,vv) = parseApp dom
    in  if sameTerm f (Req ["Eq"])
        then case aa
               of [t,l,r] =>
                 (case par_unif [] l r
                    of NONE => raise bluePlasticHammerWaaaaah
                     | SOME sbst =>
                       let val guess = App ((Req ["Eq","refl"],[t,l]),
                                                          [NoShow,ShowNorm])
                           val tm = MkApp ((tm,[guess]),[prVis v])
                           val (holes,tm) = sbst$>>>(holes,tm)
                           val ran = sbst$>>(subst1 guess ran)
                       in  ([],tm,ran)
                       end)
                | _ => usualGuesser holes tm v dom ran
        else usualGuesser holes tm v dom ran
    end

fun genPrologRefine guesser byThis S =
    let val b = hd (#1 S)
        val gid = bid b
        val targ = $!(bCT b)
        val Ty = type_of_constr byThis
        val hi = safeNumber S holeName 1
        fun refine i holes tm ty =
            case par_unif [] ty targ
              of SOME sbst => (sbst,(holes,tm))
               | NONE => case whnf ty
                           of Bind ((Pi,v),nam,dom,ran) =>
                              let val (holes,tm,ran) =
                                      guesser holes tm v dom ran
                              in  refine (i+1) holes tm ran
                              end
                            | Bind ((Sig,_),nam,fst,snd) =>
                              let val fstTm = Proj (Fst,tm)
                                  val sndTm = Proj (Snd,tm)
                                  val sndTy = subst1 fstTm snd
                              in  refine i holes sndTm sndTy
                                  handle bluePlasticHammerWaaaaah =>
                                  refine i holes fstTm fst
                              end
                            | _ => raise bluePlasticHammerWaaaaah
        val (sbst,trick) = refine hi [] byThis Ty
        val trick = sbst$>>>trick
        val realTrick = sbst$>>>trick
    in  (#1 realTrick,sbst$>>>((gid \ realTrick) S))
    end

val prologRefine = genPrologRefine usualGuesser

fun prologSplitSigHole (S as ([],_)) = ([],S)
  | prologSplitSigHole (S as (b::_,_)) =
    let val id = bid b
        val _ = if (#1 (ref_bd b))=HoleBV then () else failwith "not a hole"
        val (bC,bT) = bCT b
        val oldTy = ref_typ b
        val (holeList,spareList) = vooctxtrec
           {hitBot = fn _ => ([],[]),
            hitDom = voocontinue,
            hitVoo = fn (_,D) => fn b => fn _ => fn rect =>
                     let val (holes,spares) = rect ()
                     in  case (ref_bind b,spares)
                           of        (Sig,[]) =>
                              let val b = b<:(HoleBV,"",Bot,$!D)
                              in  (b::holes,[])
                              end
                            | _ => (holes,b::spares)
                     end} bC
        val nh = noo (HoleBV,"") id (spareList,bT)
        fun mkT [] l = l
          | mkT (h::t) l = mkT t ((Ref h)::l)
        val trick = MkTuple (oldTy,mkT holeList [Ref nh])
        val holes = nh::holeList
    in  (holes,(id \ (holes,trick)) S)
    end

fun outroHole id (S as ([],_)) = S
  | outroHole id (S as (b::C,T)) =
    if (#1 (ref_bd b))=HoleBV
    then let val (C',below) = vooctxtrec
                 {hitBot = fn b => ([],b),
                  hitDom = fn _ => fn b => fn t => fn _ => ([],b::t),
                  hitVoo = fn _ => fn x => fn _ => fn rect =>
                         ((cons (case #1 (ref_bd x)
                                   of (Lda,_) => pify x
                                    | (Hole,Def) => holesigv x
                                    | _ => failwith "bad outro"))**iota)
                           (rect ())} C
             val (hC,hT) = bCT b
             val outH = noo (HoleBV,"") id (hC@C',hT)
             val (pis,sigs) = filter (fn b => (ref_bind b)=Pi) C'
             val (ldas,(zappi,_)) = copyCtxt ldify pis
             val (zapsig,zap1b) = vooctxtrec
                 {hitBot = const ([],Ref outH), hitDom = voocontinue,
                  hitVoo = fn _ => fn x => fn _ => fn rect =>
                           let val (zs,zb) = rect ()
                           in  case #1 (ref_bd x)
                                 of (Pi,v) => (zs,MkApp ((zb,
                                                          [zappi%>>(Ref x)]),
                                                         [prVis v]))
                                  | (Sig,_) => ((x,Proj (Fst,zb))::zs,
                                                Proj (Snd,zb))
                                  | _ => failwith "bad outro"
                           end} C'
             val zaphole = (b,zap1b)::zapsig
             val (ldas,T) = zaphole%>>>(ldas,zappi%>>T)
             val (C2,T2) = vooetastate (ldas@[outH],T)
         in  (C2@below,T2)
         end
    else S

fun prologRetreat id S = on S [outroHole id,domvoo id,voosubdef id]

fun genPrologTopHole _ 0 S = S
  | genPrologTopHole _ _ (S as ([],_)) = S
  | genPrologTopHole guesser depth (S as (b::rest,_)) =
    if (#1 (ref_bd b))<>HoleBV then S else
   (let val (newHoles,S') = vooctxtrec
            {hitBot = fn _ => raise Prolog,
             hitDom = voocontinue,
             hitVoo = fn _ => fn b => fn _ => fn rect =>
             genPrologRefine guesser (Ref b) S
             handle bluePlasticHammerWaaaaah => rect ()} rest
    in  genPrologSubHoles guesser (depth-1) newHoles S'
    end
    handle Prolog => S)

and genPrologSubHoles _ depth [] S = S
  | genPrologSubHoles _ depth _ (S as ([],_)) = S
  | genPrologSubHoles guesser depth (hH::tH) (S as (hB::tB,_)) =
    genPrologSubHoles guesser depth tH
    (let val bh = bid hH
         val nh = nextHole ()
         val S1 = on S [vooattack bh nh,vooIntroTac nh]
         val (holes,S2) = prologSplitSigHole S1
         val S3 = case holes
                    of [] => S2
                     | [_] => genPrologTopHole guesser depth S2
                     | _ => genPrologSubHoles guesser depth holes S2
     in  prologRetreat bh S3
     end
     handle missing_voodoo => S)

val prologTopHole = genPrologTopHole usualGuesser
val prologSubHoles = genPrologSubHoles usualGuesser
