(***********************************************************************)
(********                                                       ********)
(********        tactics for compiling deptype funky progs      ********)
(********                                                       ********)
(***********************************************************************)

(* Problems come in the form:

   Let prob ?
     Sig f1 : some functional type
     ..
     Sig e1 : Pi xx . Let rr . (fi xx rr) = (blah xx rr)
     ..
     unit

   where the fi are functions to be (mutually) defined
   and the ei are the equations they must satisfy *)

(* Tactique Dale solves all the equations vulnerable to beta-0 *)

(* Tactique Eduardo requires an arg xij to be designated the target
   for each fi; further, the xij must each belong to a distinct branch
   of a mutual datatype; it clobbers by Eduardo's trick, then does
   case splitting until the constructors are out of the way, then it removes
   that recursion from the equations, possibly solving them, but otherwise
   dividing the problem into subproblems of the same kind... *)

type pmNames = {FTN:string,FN:string,LETN:string,FEQN:string,ITLN:string,
                ARGN:string}

val usualPmNames = {FTN="T",FN="f",LETN="F",FEQN="e",ITLN="itl",ARGN="x"}

fun parseProgProb ({FTN,FN,LETN,FEQN,ITLN,ARGN}:pmNames) prob S =
    let val pb = fetch S prob
        val _ = if (#1 (ref_bd pb))=HoleBV then () else failwith "not a hole"
        val pT = ref_typ pb
        val U = Req ["unit"]
        val E = Req ["Eq"]
        fun piLet p l (S as (_,Bind ((Pi,_),_,_,_))) =
            piLet (p+1) l (vooin (ARGN,p) S)
          | piLet p l (S as (_,Bind ((Let,Def),_,_,_)))=
            piLet p (l+1) (vooin (ITLN,l) S)
          | piLet _ _ S = S
        fun fnEq f e (S as (C,Bind ((Sig,_),nam,dom,_))) ux =
            let val (DC,DT) = piLet 1 1 ([],dom)
                val (tf,taa,tvv) = parseApp DT
                val isE = if sameTerm tf E
                          then case taa
                                 of [_,lhs,_] =>
                                    (case parseApp lhs
                                       of (Ref lfb,_,_) => bmem lfb C
                                        | _ => false)
                                  | _ => false
                          else false
                val (nom,f,e) = if isE then ((FEQN,e),f,e+1)
                                       else ((FN,f),f+1,e)
                val S = vooin nom S
                val _ = case (#1 S)
                          of [] => failwith "mad mad mad"
                           | (b::_) => b<!(Voo (nom,(DC,DT)))
            in  fnEq f e S ux
            end
          | fnEq f e (S as (C,T)) ux =
            if sameTerm T U then (S,ux)
            else fnEq f e (C,Bind ((Sig,Vis),"last",T,U)) true
        val fnum = safeNumber S FN 1
        val enum = safeNumber S FEQN 1
        val ((SIGC,SIGT),ux) = fnEq fnum enum ([],pT) false
        val noop = noo (HoleBV,ref_nam pb) prob (SIGC,SIGT)
        val trickTail = if ux
            then let val (tup,_) = vooctxtrec
                         {hitBot = const ([],Ref noop),
                          hitDom = voocontinue,
                          hitVoo = fn _ => fn _ => fn _ => fn rect =>
                                   let val (tup,thang) = rect ()
                                   in  (tup@[Proj (Fst,thang)],
                                        Proj (Snd,thang))
                                   end} SIGC
                 in  Tuple (pT,tup)
                 end
            else Ref noop
    in  (prob \ ([noop],trickTail)) S
    end


fun fetchAll (C,_) nam = vooctxtrec
                        {hitBot = const [],
                         hitDom = fn _ => fn _ => fn _ => fn _ => [],
                         hitVoo = fn ((s,_),_) => fn b => fn _ => fn rect =>
                                 (if s=nam then cons b else iota) (rect ())} C

fun hitEm nam f S =
    on S (map (fn b => f (bid b)) (fetchAll S nam))

fun solveUnits (S as (C,_)) =
    let val (V,U) = Require ["unit","void"]
        val S = vooctxtrec
           {hitBot = fn _ => S,
            hitDom = fn _ => fn _ => fn _ => fn _ => S,
            hitVoo = fn (id,_) => fn b => fn _ => fn rect =>
                    (if (#1 (ref_bd b))=HoleBV andalso (sameTerm (ref_typ b) U)
                     then (id \ ([],V)) else iota) (rect ())} C
    in  S
    end

fun Dale ({FTN,FN,LETN,FEQN,ITLN,ARGN}:pmNames) subgoal progRef S =
    let exception noDale
        fun daleEq eqn S =
           (let val (C,E) = S ?! eqn
                val (q,tlr,_) = parseApp E
                val (_,L,R) = case tlr
                        of [T,L,R] => (T,L,R)
                                 | _ => failwith "badly formed equation"
                val (LL,_,_) = parseApp L
                val LLid = bid (unRef LL)
                val (Lf,Laa,Lvv) = parseApp (vooWhnf L)
                val FB = unRef Lf
                val _ = if (#1 (ref_bd FB))=HoleBV then ()
                        else failwith "lhs not flexible"
                val Fid = bid FB
                fun mkBits (ha::ta) (hv::tv) (okv,ldas,zap) =
                   let val b = unRef ha
                       val _ = if bmem b C then () else raise noDale
                       val id = bid b
                       val _ = if member id okv
                               then failwith "lhs nonlinear"
                               else ()
                       val v = case hv of ShowNorm => Vis | _ => Hid
                       val b' = noo ((Lda,v),ref_nam b) id
                                ([],zap%>>(ref_typ b))
                   in  mkBits ta tv (id::okv,b'::ldas,(b,Ref b')::zap)
                   end
                 | mkBits _ _ X = X
               val (okVoos,ldas,zap) = mkBits Laa Lvv ([],[],[])
               val R' = zap%>>R
               fun check b = (((bid b);(not (bmem b ldas))) handle _ => false)
               val _ = if voofold false (fn x => fn y => x orelse y) check R'
                       then raise noDale
                       else ()
               val soln = vooetastate (ldas,R')
           in  on S
              [Fid \ soln,
               vooattack eqn ("zim",1),
               vooIntroTac ("zim",1),
               vooRefineTac ("zim",1) "goner" (?"%Eq refl%"),
               vookcatta eqn,
               fn S => ((progRef:=true);S)]
           end
           handle _ => S)
    in  on S
       [vooattack subgoal ("qvernik",1),
        vooSplitSigHole ("qvernik",1),
        hitEm FEQN daleEq,
        solveUnits,
        prologRetreat subgoal]
    end

fun legoDale () =
    let val progRef = ref false
        val DALED = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
                   [parseProgProb usualPmNames ("goal",1),
                    Dale usualPmNames ("goal",1) progRef]
    in  if (!progRef) then vooLegoRefine [("type",1),("blah",1)] DALED
        else ()
    end

fun pmElimNames ({FTN,FN,LETN,FEQN,ITLN,ARGN}:pmNames) =
   ({A="a",EQN="eqn",H="h",ITER=ARGN^"_aux",P="p",PHI="Phi",PRED=ARGN^"_pat",
     SUBGOAL=FN,Y="y"}:elimComponentNames)

fun pmQElimNames ({FTN,FN,LETN,FEQN,ITLN,ARGN}:pmNames) =
   ({A="a",EQN=FEQN^"_eqn",H="h",ITER=ARGN^"_aux",P="p",PHI="Phi",
     PRED=ARGN^"_pat",SUBGOAL=FEQN,Y="y"}:elimComponentNames)

fun letAbsResTy ({FTN,FN,LETN,FEQN,ITLN,ARGN}:pmNames) subg targ S =
    let val (C,T) = S ?! subg
        val (above,below) = vooctxtrec
            {hitBot = fn _ => raise missing_voodoo,
             hitDom = voocontinue,
             hitVoo = fn (id,_) => fn b => fn t => fn rect =>
                      if id=targ then ([],b::t)
                                 else ((cons b)**iota) (rect ())} C
        val relv = below
        val (ldas,(zap,_)) = copyCtxt ldify relv
        val (above,T) = zap%>>>(above,T)
        val letb = noo ((Let,Def),FTN) (FTN,#2 subg) (above@ldas,T)
        val (aa,vv) = ArgsAndVis iota relv
        val holeb = noo (HoleBV,FN) subg (below,MkApp ((Ref letb,aa),vv))
    in  (subg \ ([holeb,letb],Ref holeb)) S
    end

fun freezeNam nam (S as (C,_)) = ((vooctxtrec
   {hitBot = const (), hitDom = voocontinue,
    hitVoo = fn ((s,_),_) => fn b => fn _ => fn rect =>
             ((if s=nam then (ref_frz b):=Froz else ());
              (rect ()))} C); S)

fun unfreezeNam nam (S as (C,_)) = ((vooctxtrec
   {hitBot = const (), hitDom = voocontinue,
    hitVoo = fn ((s,_),_) => fn b => fn _ => fn rect =>
             ((if s=nam then (ref_frz b):=UnFroz else ());
              (rect ()))} C); S)

fun handyClob pmNames rule after subg targ S =
    let val target = pick S subg targ
        val S = freezeNam (#FTN pmNames) S
        val (subgc,S) = holyClobber RightStrat (pmElimNames pmNames) true rule
                        (subg,target,NONE) S
        val S = foldr after S subgc
        fun blep b S = KJunifyTestMore (const true) (bid b) S
        val S = foldr blep S subgc
    in  unfreezeNam (#FTN pmNames) S
    end

fun edClob pmNames subg targ S =
    let val tnam = ref_nam (unRef (#1 (parseApp (#2 (S ?! subg ?! targ)))))
        val rule = Req [tnam,"eduardo"]
        val aux = Req [tnam,"aux"]
        val auxn = #ITER (pmElimNames pmNames)
        val auxi = safeNumber S auxn 1
        fun nobble b S =
            let val (C,_) = bCT b
                val _ = vooctxtrec
                   {hitBot = const auxi, hitDom = voocontinue,
                    hitVoo = fn ((s,i),(c,t)) => fn b => fn _ => fn rect =>
                             let val auxi = rect ()
                             in  if sameTerm (voohead t) aux
                                 then ((b<!(Voo ((auxn,auxi),(c,t))));(auxi+1))
                                 else auxi
                             end} C
            in  S
            end
    in  handyClob pmNames rule nobble subg targ S
    end

fun makeLet id jd (S as (C,T)) =
    let val C' = vooctxtrec
                {hitBot = iota, hitDom = voocontinue,
                 hitVoo = fn (kd,D) => fn b => fn t => fn rect =>
                          if kd<>id then b::(rect ())
                          else let val newb = noo (HoleBV,"") id D
                                   val b = (b<:((Let,Def),ref_nam b,Ref newb,
                                                ref_typ b))
                                             <!(Voo (jd,([],Ref newb)))
                               in  b::newb::t
                               end} C
    in  (C',T)
    end

fun Split (pmNames as {FTN,FN,LETN,FEQN,ITLN,ARGN}:pmNames) eqn S =
   (let val (C,E) = S ?! eqn
        val (q,tlr,_) = parseApp E
        val (_,L,R) = case tlr
                        of [T,L,R] => (T,L,R)
                         | _ => failwith "ganged agley"
        val (Lf,Laa,Lvv) = parseApp (vooWhnf L)
        val FB = unRef Lf
    in  if (#1 (ref_bd FB))=HoleBV then
    let val Fid = bid FB
        val (FC,FT) = bCT FB
        val auxn = #ITER (pmElimNames pmNames)
        val (zap,aux,_) = vooctxtrec
            {hitBot = const ([],Bot,Laa), hitDom = voocontinue,
             hitVoo = fn ((s,_),_) => fn b => fn _ => fn rect =>
                      let val (zap,aux,laa) = rect ()
                      in  case laa
                            of [] => failwith "bad equation"
                             | (lah::lat) =>
                               let val aux = if s=auxn then #2 (bCT b)
                                                       else aux
                               in ((b,vooWhnf lah)::zap,aux,lat)
                               end
                      end} FC
        val aux = case vooDnf>>aux
                    of Bot => failwith "couldn't find auxiliary data"
                     | x => x
        fun splot (Bind ((Sig,_),_,h,t)) = (splot h)@(splot t)
          | splot (Bind (_,_,_,t)) = splot t
          | splot x = let val (f,aa,_) = parseApp x
                      in (if (#1 (tid f))<>FTN then raise missing_voodoo
                          else [])
                          handle missing_voodoo =>
                         (let val b = unRef (last aa)
                          in  if bmem b FC
                              then let val (f,aa,_) = parseApp (zap%>>(Ref b))
                                   in   case (f,voohead (type_of_constr f))
                                          of (Ref c,Ref ct) =>
                                             if mem (ref_nam c) (ref_deps ct)
                                             then [(bid b,ref_nam ct)]
                                             else []
                                           | _ => []
                                   end
                              else []
                          end
                          handle _ => [])
                      end
    in  case splot aux
          of [] => S
           | (targ,inam)::_ =>
             on S
            [freezeNam LETN,
             handyClob pmNames (Req [inam,"cases"]) (const iota) (bid FB) targ,
             unfreezeNam LETN,
             Split pmNames eqn]
    end else S
    end
    handle missing_voodoo => S)

fun Splut (pmNames as {FTN,FN,LETN,FEQN,ITLN,ARGN}:pmNames) eqn S =
   (let val (C,E) = S ?! eqn
        val (q,tlr,_) = parseApp E
        val (_,L,R) = case tlr
                        of [T,L,R] => (T,L,R)
                         | _ => failwith "ganged agley"
        val (Lf,Laa,Lvv) = parseApp (vooWhnf L)
        val FB = unRef Lf
    in  if (#1 (ref_bd FB))=HoleBV then S else
    let val qElimNames = (pmQElimNames pmNames)
        val (PC,PT) = parselim S qElimNames (type_of_constr Lf)
        val qP = #P qElimNames
        val qY = #Y qElimNames
        val (target,_) = vooctxtrec
            {hitBot = const (Bot,Laa), hitDom = voocontinue,
             hitVoo = fn ((s,_),_) => fn _ => fn _ => fn rect =>
                      let val (tg,a,aa) =
                              case rect ()
                                of (_,[]) => failwith "ganged agley"
                                 | (x,h::t) => (x,h,t)
                      in  if s=qP orelse s=qY then (a,aa) else (tg,aa)
                      end} PC
        fun blep b S = on S
                      [KJunifyTestMore (const true) (bid b),
                       Split pmNames (bid b)]
        val (subgs,S) = holyClobber MiddleStrat qElimNames true Lf
                                   (eqn,target,NONE) S
    in  foldr blep S subgs
    end
    end
    handle missing_voodoo => S)

fun Splat (pmNames as {FTN,FN,LETN,FEQN,ITLN,ARGN}:pmNames) eqn S =
    let val EB = fetch S eqn
        val (C,E) = bCT EB
        val (q,tlr,qvv) = parseApp E
        val (T,L,R) = case tlr
                        of [T,L,R] => (T,L,R)
                         | _ => failwith "ganged agley"
        val (Lf,Laa,Lvv) = parseApp (vooWhnf L)
        val FB = unRef Lf
        val _ = if (#1 (ref_bd FB))=HoleBV then () else failwith "ganged agley"
        val Fid = bid FB
        val (FC,FT) = bCT FB
        val auxn = #ITER (pmElimNames pmNames)
        val (itLets,fArgs,spArgs) = vooctxtrec
            {hitBot = const ([],[],Laa), hitDom = voocontinue,
             hitVoo = fn ((s,i),_) => fn b => fn _ => fn rect =>
                      let val (itl,faa,laa) = rect ()
                      in  case laa
                            of [] => failwith "bad equation"
                             | (lah::lat) =>
                                if s=auxn
                                then let val nl = noo ((Let,Def),"itl")
                                                      (ITLN,i)
                                                      ([],vooWhnf lah)
                                     in (nl::itl,faa@[Ref nl],lat)
                                     end
                                else (itl,faa@[lah],lat)
                      end} FC
        fun doAbs recC b aa vv =
            let fun chop (Bind (_,_,_,r)) (h1::t1,h2::t2) =
                    (((cons h1)**(cons h2))**iota) (chop r (t1,t2))
                  | chop _ X = (([],[]),X)
                val ((aaf,vvf),(aab,vvb)) = chop (ref_typ b) (aa,vv)
                val Ty = type_of_constr (MkApp ((Ref b,aaf),vvf))
                val whTy = vooWhnf Ty
                val i = case recC
                          of [] => 1
                           | (b::_) => (#2 (bid b))+1
                val hB = noo (HoleBV,"rec") ("rec",i) ([],Ty)
                val lB = ((Let,Def),"REC",Ref hB,whTy):!
                         (Voo (("REC",i),([],Ref hB)))
            in (lB::hB::recC,MkApp ((Ref lB,aab),vvb))
            end
        fun mangR RC (recC,t) =
           (case t
              of Ref b => (recC,t)
               | App _ =>
                 let val (f,aa,vv) = parseApp t
                     val (recC,aa') = manglR RC (recC,aa)
                     val (recC,f) = mangR RC (recC,f)
                 in  case f
                       of Ref b => 
                         (case ref_kind b
                            of Voo ((s,i),_) =>
                               if s=LETN then doAbs recC b aa' vv
                               else (recC,MkApp ((f,aa'),vv))
                             | _ => (recC,MkApp ((f,aa'),vv)))
                        | _ => (recC,MkApp ((f,aa'),vv))
                 end
               | Proj (k,t) =>
                 let val (recC,t) = mangR RC (recC,t)
                 in  (recC,Proj (k,t))
                 end
               | Tuple (f,aa) =>
                 let val (recC,aa') = manglR RC (recC,aa)
                     val (recC,f) = mangR RC (recC,f)
                 in  (recC,MkTuple (f,aa'))
                 end

               | _ => failwith "too stupid right now")
        and manglR RC (recC,[]) = (recC,[])
          | manglR RC (recC,h::t) =
            let val (recC,h) = mangR RC (recC,h)
            in (iota**(cons h)) (manglR RC (recC,t))
            end
        val trick = mangR [] ([],R)
        val (recHoles,_) = filter (fn b => (#1 (ref_bd b))=HoleBV) (#1 trick)
        val L' = MkApp ((Ref (*LEXB*)FB,fArgs@spArgs),Lvv)
        val theFNs = fetchAll S FN
        val theFTNs = fetchAll S FTN

        val (STUFF,Rthing) = on ((#1 trick)@itLets@C@theFNs@theFTNs,#2 trick)
                            [freezeNam FTN, freezeNam ITLN,
                             genPrologSubHoles reflGuesser
                                              (cnstr_size R) recHoles,
                             unfreezeNam FTN,
                             hitEm "REC" voosubdef,
                             unfreezeNam ITLN]

        val R' = Rthing

        val _ = case (par_unif [] L L',par_unif [] R R')
                  of (SOME _,SOME _) => ()
                   | _ => failwith "unexpected attack of conscience"

        val itlVals = foldl (fn l => fn b => (ref_val b)::l) [] itLets
        val itlViss = map (const ShowNorm) itlVals
        val itPis = map letpiv itLets
        val nooq = noo (HoleBV,ref_nam EB) eqn
                       (vooCopy (itPis@C,App ((q,[T,L',R']),qvv)))
        val (oaa,ovv) = ArgsAndVis iota C
        val (ldas,(zap,_)) = copyCtxt ldify C
        val trick = zap%>>(MkApp ((Ref nooq,oaa@itlVals),ovv@itlViss))
        val (ldas,trick) = vooetastate (ldas,trick)
    in  on S
       [eqn \ (ldas@[nooq],trick)]
    end

fun whnfTail id S =
    let val b = fetch S id
        val (C,T) = bCT b
        val T = vooWhnf T
        val v = $!(C,T)
        val t = type_of_constr v
        val b = case ref_bd b
                  of (bv,nam,dom,_) => b<:
                     (if bv=HoleBV then (bv,nam,dom,v) else (bv,nam,v,t))
        val b = b<!(Voo (id,(C,T)))
    in  S
    end

fun Eduardo (pmNames as {FTN,FN,LETN,FEQN,ITLN,ARGN}:pmNames)
            subgoal targets S =
    let fun edify (S as (C,_)) = #1 (vooctxtrec
           {hitBot = fn _ => raise missing_voodoo,
            hitDom = fn _ => fn _ => fn _ => fn _ => (S,targets),
            hitVoo = fn (id as (s,i),_) => fn _ => fn _ => fn rect =>
                    (case rect ()
                       of R as (S,[]) => R
                        | R as (S,targ::tt) =>
                          if s=FN
                          then (on S
                               [letAbsResTy pmNames (FN,i) targ,
                                makeLet (FN,i) (LETN,i),
                                freezeNam LETN,
                                edClob pmNames id targ,
                                (fn S => vooDnf>>>S),
                                unfreezeNam LETN,
                                whnfTail (LETN,i)],tt)
                          else R)} C)

        fun tidyUp S =
            let val S = on S
                       [hitEm FTN voosubdef,
                        hitEm LETN voosubdef]
                val esfs = vooctxtrec
                   {hitBot = const [], hitDom = voocontinue,
                    hitVoo = fn (id as (s,i),(_,T)) => fn _ => fn _ =>
                             fn rect =>
                            (if s = FEQN
                             then let val (fs,_) = filter (fn (n,_) => n=FN)
                                                  (voodep1l T)
                                  in  cons ([id],fs)
                                  end
                             else iota) (rect ())} (#1 S)
                fun merge1 EEFF l [] false = (EEFF,l)
                  | merge1 EEFF l [] true = merge1 EEFF [] l false
                  | merge1 (ee1,ff1) l ((EEFF as (ee2,ff2))::t) flag =
                    if joint ff1 ff2
                    then merge1 (union ee1 ee2,union ff1 ff2) l t true
                    else merge1 (ee1,ff1) (EEFF::l) t flag
                fun merge [] = []
                  | merge (h::t) =
                    let val (c,r) = merge1 h [] t false
                    in  c::(merge r)
                    end
                val plan = merge esfs
                val U = Req ["unit"]
                fun clump (ee,ff) (S as (C,T)) =
                    let val these = ee@ff
                        val nh = noo (HoleBV,"clump") ("clump",#2 (hd ff))
                                     ([],U)
                        val (cl,sp,zap,_,def,base) = vooctxtrec
                           {hitBot = fn _ => raise missing_voodoo,
                            hitDom = fn _ => fn b => fn t => fn _ =>
                                     ([],[],[],Ref nh,b,t),
                            hitVoo = fn (id,_) => fn b => fn _ => fn rect =>
                                     let val (cl,sp,zap,prj,def,base) = rect ()
                                     in  if member id these
                                         then ((holesigv b)::cl,sp,
                                               (b,Proj (Fst,prj))::zap,
                                               Proj (Snd,prj),def,base)
                                         else (cl,b::sp,zap,prj,def,base)
                                     end} C
                        val clS = (cl,U)
                        val nh = (nh<:(HoleBV,"clump",ref_val nh,$!clS))
                                    <!(Voo (bid nh,clS))
                        val T = zap%>>T
                    in (sp@(def::nh::base),T)
                    end
                val S = foldr clump S plan                
            in  domvoo subgoal S
            end
    in  on S
       [vooattack subgoal ("qvernik",1),
        vooSplitSigHole ("qvernik",1),
        edify,
        hitEm FEQN (Split pmNames),
        hitEm FEQN (Splut pmNames),
        hitEm FEQN (Splat pmNames),
        solveUnits,
        tidyUp]
    end

fun legoEduardo legoTargs =
    let fun spotOne nam num C = #1 (vooctxtrec
           {hitBot = fn _ => const (("",0),false,1), hitDom = voocontinue,
            hitVoo = fn (id,_) => fn b => fn _ => fn rect => fn deps =>
                     case (rect () (union (voodep1l (ref_typ b)) deps))
                       of R as (_,true,_) => R
                        | R as (_,_,i) =>
                          if num=0 andalso nam=(ref_nam b)
                          then (id,true,0)
                          else if member id deps
                          then R
                          else if num=i
                          then (id,true,0)
                          else (("",0),false,i+1)} C [])
        fun spot S id legoTargs =
            let val (C,_) = S ?! id
            in  #1 (vooctxtrec
               {hitBot = const ([],legoTargs), hitDom = voocontinue,
                hitVoo = fn (_,(dc,_)) => fn _ => fn _ => fn rect =>
                         case rect ()
                           of R as (_,[]) => R
                            | (tt,h::t) =>
                              let val (nam,num) = ("",atoi h)
                                      handle Convert => (h,0)
                                  val tg = spotOne nam num dc
                              in  if tg=("",0) then failwith "target not found"
                                  else (tt@[tg],t)
                              end} C)
            end
        val EDDED = on (vooStealGoal [("type",1),("blah",1)] ("goal",1))
                   [parseProgProb usualPmNames ("goal",1),
                    fn S => Eduardo usualPmNames ("goal",1)
                                   (spot S ("goal",1) legoTargs) S,
                    voosubdef ("goal",1)]
    in  vooLegoRefine [("type",1),("blah",1)] EDDED
    end

fun legoSaveReductions nameList = case (getFinishedProof ())
 of NONE => failwith("cannot register reductions: no complete proof")
  | SOME ((n,lg),vt as (v,t)) =>
    let val OLDCTXT = getNamespace ()
    in
    let val v = if n="" then v
                else ((extendCxtGbl Bnd (Let,Def) (UnFroz,lg) [] n vt);
                      (message (n^" saved unfrozen"));
                      (Ref (hd (getNamespace ()))))
        val oldGOAL = vooGoal [("type",1),("blah",1)] ("goal",1) ([],t)
        val ppp = parseProgProb usualPmNames ("goal",1) oldGOAL
        val (C,_) = ppp ?! ("goal",1)
        val FN = #FN usualPmNames
        val EQ = Req ["Eq"]
        val (_,_,zap) = vooctxtrec
           {hitBot = const (v,nameList,[]), hitDom = voocontinue,
            hitVoo = fn (_,D) => fn b => fn _ => fn rect =>
                     let val (v,nn,zap) = rect ()
                         val thing = Proj (Fst,v)
                         val rest = Proj (Snd,v)
                     in  if (isItA FN b) then
                         let val h = (hd nn
                                      handle _ => failwith "not enough names")
                             val ty = type_of_constr thing
                             val _ = case par_unif [] ty ($!D)
                                     of NONE =>
                                        failwith "unexpected type error"
                                      | _ => ()
                             val _ =
                             ((extendCxtGbl Bnd (Let,Def) (UnFroz,lg) [] h
                              (thing,ty));
                             (message (h^" saved unfrozen")))
                         in (rest,tl nn,(b,Ref (hd (getNamespace ())))::zap)
                         end else (rest,nn,zap)
                     end} C
        val FEQN = #FEQN usualPmNames
        val (ldas,reds) = vooctxtrec
           {hitBot = const ([],[]), hitDom = voocontinue,
            hitVoo = fn (_,D) => fn b => fn _ => fn rect =>
                     let val (ldas,reds) = rect ()
                         val (DC,DT) = zap%>>>D
                     in  if (isItA FEQN b) then
                         let val R = case DT
                                       of App ((f,[_,l,r]),_) =>
                                          if sameTerm f EQ
                                             andalso (case par_unif [] l r
                                             of NONE => false | _ => true)
                                          then LabVT (RedPr,l,r)
                                          else failwith "doesn't reduce"
                                        | _ => failwith "bad equation"
                         in (foldr (fn x => cons (ldify x)) ldas DC,R::reds)
                         end else (ldas,reds)
                     end} C
        val redThing = $!(ldas,CnLst reds)
        val _ = vooAddReductions redThing
        val _ = Freeze nameList
        val _ = map (fn s => message (s^" frozen")) nameList
        val _ = init_history ()
    in  ()
    end
    handle x => ((putNamespace OLDCTXT);(raise x))
    end

(*
val _ = ConorTools.Eduardo := legoEduardo
*)