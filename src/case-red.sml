(*************************************************************************)
(**********                                                     **********)
(**********         Conor's case reduction mechanism            **********)
(**********                                                     **********)
(*************************************************************************)

fun stripBind (Bind (_,_,_,r)) = stripBind r
  | stripBind x = x

fun MarkConstructors dt =
    let val (_,casesType) = Require [dt,"cases"]
        val (casesPrems,casesConc) = introall whnf "X" 1 ([],casesType)
        val Phi = case casesConc
                    of App ((Ref br,_),_) => br
                     | _ => failwith "markup disaster: parsing cases"
        val (alist,_) = vooctxtrec
            {hitBot = fn _ => ([],0),
             hitDom = fn _ => fn _ => fn _ => fn _ => ([],0),
             hitVoo = fn (_,(_,T)) => fn _ => fn t => fn rect =>
                      let val R as (al,i) = rect ()
                      in  case stripBind T
                            of App ((Ref br,xs),_) =>
                               if br=Phi
                               then case last xs
                                      of Ref b => ((ref_nam b,i)::al,i+1)
                                       | App ((Ref b,_),_) =>
                                         ((ref_nam b,i)::al,i+1)
                                       | _ => failwith "markup disaster: parse"
                               else R
                             | _ => R
                      end} casesPrems
        val _ = map (fn (nam,num) =>
                     let val b = case ?nam
                                   of Ref b => b
                                    | _ => failwith "markup disaster: lookup"
                         val Bd {bd=bd,deps=deps,frz=frz,ts=ts,param=param,
                                 kind=kind} = !b
                     in  b := Bd {bd=bd,deps=deps,frz=frz,ts=ts,param=param,
                                 kind=Constructor num}
                     end
                    ) alist
    in ()
    end

val _ = MarCons := MarkConstructors (* who needs modules anyway? *)
(***********************
fun caseLoad 0 x = x
  | caseLoad n (xs,y::ys,r) = caseLoad (n-1) (y::xs,ys,r)
  | caseLoad _ _ = failwith "Too few arguments!"

fun cKind b = case ref_kind b
                of Constructor i => i
                 | _ => failwith "Not a constructor!"

fun bHeadArgs2 (Ref b) ys = (b,ys)
  | bHeadArgs2 (App ((f,xs),_)) ys = bHeadArgs2 f (xs@ys)
  | bHeadArgs2 _ _ = failwith "Not first order!"

fun bHeadArgs x = bHeadArgs2 x []

fun stackUp [] ys = ys
  | stackUp (x::xs) ys = stackUp xs (x::ys)

fun caseCaseCollect i c [] = []
  | caseCaseCollect i c ((stk,args,r)::xs) =
    let val xs' = caseCaseCollect i c xs
        val (b,cargs) = bHeadArgs (nth stk i)
    in  if c=(cKind b)
        then ((stackUp cargs stk,args,r)::xs')
        else xs'
    end

val FakeB = ref (Bd {bd=((Lda,Vis),"",Bot,Bot),deps=[],frz=ref Froz,ts=(~1),
                       param=Local,kind=Voo (b42,([],Bot))})

fun makeVCtxt [] = []
  | makeVCtxt ((Ref b)::ys) =
   (case ref_kind b
      of Voo _ => b::(makeVCtxt ys)
       | _ => FakeB::(makeVCtxt ys))
  | makeVCtxt (_::ys) = FakeB::(makeVCtxt ys)

fun caseReturn [(stk,[],rhs)] =
    (cReturn ($! (makeVCtxt stk,rhs)),length stk)
  | caseReturn _ = failwith "Not ready to return!"

fun caseBug [] = (cBug,0)
  | caseBug _ = failwith "Still a case to answer!"

fun makeProgram RR (cLoad (n,p)) =
    let val (p,ss) = makeProgram (map (caseLoad n) RR) p
    in  (cLoad (n,p),ss)
    end
  | makeProgram RR (cCase (i,pa)) =
    let val l = Array.length pa
        fun mang ss c = if c < l
        then let val (p,ss') = makeProgram (caseCaseCollect i c RR)
                                           (Array.sub (pa,c))
                 val _ = Array.update (pa,c,p)
             in  mang (max (ss,ss')) (c+1)
             end
        else ss
    in (cCase (i,pa),mang 0 0)
    end
  | makeProgram RR cBug = caseBug RR
  | makeProgram RR (cReturn _) = caseReturn RR

fun CaseProgram x _ p =
    let val b = case ?x
                  of Ref b => b
                   | _ => failwith "No reductions!"
        val (RC,RT) = introall iota "X" 1 ([],get_reductions b)
        val RR = case RT
                   of CnLst x =>
                      map (fn LabVT (RedPr,App ((_,l),_),r) => ([],l,r)
                            | _ => failwith "Bad Reductions") x
                    | _ => failwith "No Reductions!"
        val (p,ss) = makeProgram RR p
        val Bd {bd=bd,deps=deps,frz=frz,ts=ts,param=param,
                                 kind=kind} = !b
    in  b := Bd {bd=bd,deps=deps,frz=frz,ts=ts,param=param,
                 kind=Program (ss,p)}
    end

*******************************)
