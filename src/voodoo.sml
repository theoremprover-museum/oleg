val global_pvp = parser_var_pack ()
fun hole_pvp hole ty =
    case global_pvp ty
      of Var ((n,_),t) => Var ((n,Ref hole),t)
       | _ => failwith "mad mad mad!"

(* Lots of infix operators in this file. I've tried to keep them making
   some sort of sense, but it's tricky. *)

fun Req tag = #1 (Require tag)

infix <- (* assignment to a binder, checking it's a Dom or Voo *)
infix <: (* update binder_data *)
infix <! (* update kind *)
infix :! (* new ref with given binder_data and kind *)

val HoleBV = (Hole,Def)
fun holy b = (#1 (ref_bd b))=HoleBV andalso !(ref_frz b)=UnFroz

fun B <- b = case ref_kind B
               of Voo _ => ((B := b);B)
                | Dom _ => ((B := b);B)
                | _ => bug "Bad Ass Mother!"

fun (B as ref (Bd {kind,deps,frz,ts,param,...})) <: bd =
    B <- (Bd {bd=bd,deps=deps,frz=frz,ts=ts,param=param,kind=kind})

fun (B as ref (Bd {bd,deps,frz,ts,param,...})) <! k =
    B <- (Bd {bd=bd,deps=deps,frz=frz,ts=ts,param=param,kind=k})

fun bd :! k = ref (Bd {bd=bd,kind=k,ts=timestamp(),deps=[],frz=ref UnFroz,
                       param=Local})

fun !!B =
    let val bdB = ref_bd B
        val b = bdB:!(ref_kind B)
    in  case bdB
          of ((Hole,Def),nam,Var (_,x),t) =>
             b<:((Hole,Def),nam,hole_pvp b x,t)
           | _ => b
    end

val VooBase = ref (Bd {bd=((Pi,Vis),"",Bot,Bot),deps=[],frz=ref Froz,ts=(~1),
                       param=Local,kind=VooDont})

val b42 = ("bogus",42)  (* standard absent id *)

fun start (x:cnstr) = (VooBase::(getNamespace()),x)

exception missing_voodoo

fun vooctxtrec {hitVoo,hitDom,hitBot} C =
    let fun lazy ctxt () = (* crucially lazy *)
            case ctxt
              of [] => hitBot []
               | (ref (Bd {kind=VooDont,...}))::_ => hitBot ctxt
               | (b as ref (Bd {kind=Voo v,...}))::t =>
                 hitVoo v b t (lazy t)
               | (b as ref (Bd {kind=Dom d,...}))::t =>
                 hitDom d b t (lazy t)
               | _ => failwith "bad bad voodoo!"
    in  lazy C ()
    end

fun voocontinue _ _ _ rect = rect ()
fun voobottom _ = raise missing_voodoo

fun fetch (ctxt,_) id = vooctxtrec
                        {hitBot = voobottom,
                         hitDom = voocontinue,
                         hitVoo = fn (jd,_) => fn b => fn _ => fn rect =>
                                  if id=jd then b else rect ()} ctxt

infix ?!

fun bVoo b = case ref_kind b
               of Voo V => V
                | _ => raise missing_voodoo
val bid = (#1) o bVoo
val bCT = (#2) o bVoo

fun S ?! id = bCT (fetch S id)

fun unRef (Ref b) = b
  | unRef _ = raise missing_voodoo

val tVoo = bVoo o unRef
val tid  = (#1) o tVoo
val tCT  = (#2) o tVoo

(*
infix ?? (* wrap with a context *)
infix !? (* wrap with the context from a state *)

fun C ?? f = fn a =>
    let val old = getNamespace()
    in  let val _ = putNamespace C
            val answer = f a
            val _ = putNamespace old
        in  answer
        end
        handle x => ((putNamespace old);(raise x))
    end

fun (C,_) !? f = C??f
*)

(* None of Randy's code ever really needs to know much about the Namespace,
   'cos every Ref carries its own info with it, hence we shouldn't really
   need to wrap things all that much *)

fun voorewrite f =
    let fun $i v = case (f i v)
                     of x as Mod _ => x
                      | UMod => split i v
        and split i    (App v) = mkApp ($i) v
          | split i   (Bind v) = mkBind $ i v
          | split i    (Var v) = mkVar ($i) v
          | split i  (Tuple v) = mkTuple ($i) v
          | split i   (Proj v) = mkProj ($i) v
          | split i  (LabVT v) = mkLabVT ($i) v
          | split i  (CnLst v) = mkCnLst ($i) v
          | split i (RedTyp v) = mkRedTyp ($i) v
          | split i   (Case v) = mkCase ($i) v
          | split i         v  = UMod
    in  $0
    end

infix >> (* voorewrite *)

fun mang>>x = share (voorewrite mang) x

fun voomap f =
    voorewrite (fn i => (fn Ref b => f i b | _ => UMod))

fun voofold start joinFn bdFn =
    let fun $r           (Ref b) = joinFn (bdFn b) r
          | $r (App ((v,vl),pl)) = $$($r v) vl
          | $r  (Bind (b,s,u,v)) = $($r u) v
          | $r       (Var (j,v)) = $r v
          | $r    (Tuple (v,vl)) = $$($r v) vl
          | $r      (Proj (p,v)) = $r v
          | $r   (LabVT (l,u,v)) = $($r u) v
          | $r        (CnLst vl) = $$r vl
          | $r    (RedTyp (j,v)) = $r v
          | $r      (Case (u,v)) = $($r u) v
          | $r                 _ = r
        and $$r = foldl $ r
    in  $start
    end


local

    fun farid bunder b =
        let val bts = ref_ts b
            fun f2 [] = raise missing_voodoo
              | f2 (jts::t) =
                if bts=jts then 1+bunder
                else 1+(f2 t)
        in  f2
        end

    fun relid far near bunder b = Mod (
        Rel (vooctxtrec
             {hitBot = fn _ => farid bunder b far,
              hitDom = voocontinue,
              hitVoo = fn _ => fn c => fn _ => fn rect =>
                       if sameRef b c then 1+bunder
                       else 1+(rect ())} near))
        handle missing_voodoo => UMod

    fun justTss l = vooctxtrec
                    {hitBot = fn _ => l,
                     hitDom = voocontinue,
                     hitVoo = fn _ => fn b => fn _ => fn rect =>
                              (ref_ts b)::(rect ())}

    fun zug nam (s,i) = if nam = "" then s^(string_of_num i) else nam

    fun stoppit far (near,tip) =
        tippit far (near,(share (voomap (relid far near)) tip))
    and tippit far ([],tip) = tip
      | tippit far ((b::t),tip) =
        case ref_kind b
          of VooDont => tip
           | Voo (id,D) =>
             let val (bv,nam,_,_) = ref_bd b
             in  tippit far
                 (t,(Bind (bv,zug nam id,stoppit (justTss far t) D,tip)))
             end
           | Dom (id,V) =>
             let val (bv,nam,_,_) = ref_bd b
             in  tippit far
                 (t,(Bind (bv,zug nam id,tip,
                           stoppit ((ref_ts b)::(justTss far t)) V)))
             end
           | _ => tip

(* hmmmmmm *)
    fun holeSpot _ (Ref b) = (case ref_kind b
                               of Voo _ => failwith "bad proof term"
                                | Dom _ => failwith "bad proof term"
                                | _ => UMod)
      | holeSpot _ (Bind (bv,_,_,_)) =
        if bv=HoleBV then failwith "bad proof term"
        else UMod
      | holeSpot __ = UMod

    fun split id (ctxt,tail) = vooctxtrec
        {hitBot = voobottom, hitDom = voocontinue,
         hitVoo = fn (jd,_) => fn b => fn t => fn rect =>
                  if id=jd then (t,([b],tail))
                  else (iota**((cons b)**iota)) (rect ())} ctxt

in
    fun $! S = stoppit [] S
    fun stop S = holeSpot>>($!S)
    fun stopId id S = (iota**($!)) (split id S)
end

exception no_intro

fun voogle (bv,nam,dom,_) =
    let val (bdom,bran) =
            case bv
              of (Hole,Def) => (global_pvp dom,dom) (* must set back pointer *)
               | (_,VBot) => (Bot,dom)
               | _ => (dom,type_of_constr dom)
    in  (bv,nam,bdom,bran)
    end

fun noo (bv,nam) id D =
    let val b = (voogle (bv,nam,$!D,Bot)):!(Voo (id,D))
    in  case ref_bd b
          of ((Hole,Def),nm,Var ((n,_),x),t) =>
             b<:((Hole,Def),nm,Var ((n,Ref b),x),t)
           | _ => b
    end

fun relBang C under (Rel i) = if i<=under then UMod
                              else Mod (Ref (nth C (i-under)))
  | relBang _ _ _ = UMod

fun voomanginl redFn mangle l (C,T) =
    let fun vmil2 [] (C,T) = (C,(relBang C)>>T)
          | vmil2 ((s,i)::t) (S as (ctxt,Bind (bd as (bv,nam,dom,rng)))) =
            let val nam = mkNameGbl (if nam<>"" then nam
                                     else (s^(string_of_num i)))
                val newBd = mangle (noo (bv,nam) (s,i)
                            ([],(relBang ctxt)>>dom))
            in  vmil2 t (newBd::ctxt,redFn rng)
            end
          | vmil2 _ _ = raise no_intro
    in  vmil2 l (C,redFn T)
    end

fun voomangin mangle id = voomanginl iota mangle [id]

val vooin = voomangin iota
val vooinl = voomanginl iota iota

fun isitBd id b = id=(bid b)
    handle missing_voodoo => false

fun isit id t = id=(tid t)
    handle missing_voodoo => false

fun isItA s b = s=(#1 (bid b))

fun isItOne sl b = member (#1 (bid b)) sl

fun vid (ctxt,_) id =
    vooctxtrec
    {hitBot = voobottom,
     hitVoo = fn (jd,_) => fn b => fn _ => fn rect =>
              if id=jd then Ref b else rect (),
     hitDom = voocontinue}
    ctxt

fun mapNapp f =
    let fun ma [] y = y
          | ma (h::t) y = (f h)::(ma t y)
    in  ma
    end

fun intromangvool mang [] _ _ S = S
  | intromangvool mang names from qty S =
    let val top = from+qty
        fun mkids i = if i>=top then []
                      else mapNapp (fn s => (s,i)) names (mkids (i+1))
    in  voomanginl iota mang (mkids from) S
    end

val introvool = intromangvool iota

fun introtestmangall test mang redFn lab from (S as (C,T)) =
    let fun mkids i (ty as Bind (_,_,_,t)) =
            if test ty then (lab,i)::(mkids (i+1) (redFn t))
                       else []
          | mkids _ _ = []
    in  voomanginl redFn mang (mkids from (redFn T)) S
    end

val intromangall = introtestmangall (const true)

val introall = intromangall iota

fun introtestall test = introtestmangall test iota

fun whnfLetBlat x = case whnf x
 of Bind ((Let,Def),_,thang,body) => whnfLetBlat (subst1 thang body)
  | t => t

fun Okras bt (Bind ((b,_),_,_,_)) = (bt=b)
  | Okras _ _ = false

fun voodom id (ctxt,tail) =
    let val (pre,(b,rest,ctxt',tail')) = vooctxtrec
            {hitBot = voobottom,
             hitDom = fn _ => fn b => fn _ => fn rect =>
                      ((cons b)**iota) (rect ()),
             hitVoo = fn (jd,(ctxt',tail')) => fn b => fn t => fn rect =>
                      if id=jd
                      then ([],(b,t,ctxt',tail'))
                      else ((cons b)**iota) (rect ())} ctxt
    in  (ctxt'@((b<!(Dom (id,(pre,tail))))::rest),tail')
    end

fun domvoo id (ctxt,tail) =
    let val (pre,(b,rest,ctxt',tail')) = vooctxtrec
            {hitBot = voobottom,
             hitVoo = fn _ => fn b => fn _ => fn rect =>
                      ((cons b)**iota) (rect ()),
             hitDom = fn (jd,(ctxt',tail')) => fn b => fn t => fn rect =>
                      if id=jd
                      then ([],(b,t,ctxt',tail'))
                      else ((cons b)**iota) (rect ())} ctxt
    in  (ctxt'@((b<!(Voo (id,(pre,tail))))::rest),tail')
    end

fun vooConj S id thang =
    let val S' = voodom id S
    in  let val x = thang S'
            val _ = domvoo id S'
        in  x
        end
        handle ex => ((domvoo id S');(raise ex))
    end

datatype 'a Rev = Rev of 'a list

local
    fun revctxt l [] = l
      | revctxt l ((ref (Bd {kind=VooDont,...}))::_) = l
      | revctxt l (h::t) = revctxt (h::l) t
in
    fun rev l = Rev (revctxt [] l)
    fun unrev (Rev l) = revctxt [] l
    fun revon (Rev r) c = revctxt c r
end

fun revlen (Rev l) = length l
fun conjrev1 f a = (rev**iota) (f ((unrev**iota) a))

local
    fun usuV Vis = " : "
      | usuV Hid = " | "
      | usuV Def = " = "
      | usuV VBot = " ? "
      | usuV Guess = " ?= "
    fun bvBits (Pi,v) = ("All ",usuV v)
      | bvBits (Lda,v) = ("Lda ",usuV v)
      | bvBits (Let,v) = ("Let ",usuV v)
      | bvBits (Sig,v) = ("Sig ",usuV v)
      | bvBits (Hole,Def) = ("Hole "," : ")
      | bvBits (Hole,Guess) = ("Hole "," ?= ")
      | bvBits _ = ("Hmm"," ? ")
    fun indent 0 = ()
      | indent n = ((print "| ");(indent (n-1)))
    fun pid (s:string,i) = ((print "V-");(print s);(print (string_of_num i)))
    fun vooprint1 flag ind (Rev revved,tail) =
        case revved
          of [] => ((indent ind);
                    (if flag then print "=> " else ());
                    (legoprint tail))
           | (ref (Bd {kind=Voo (id,(dc,dt)),bd=(bv,_,_,_),...}))::rt =>
             let val (bs,vs) = bvBits bv in
             ((indent ind);(print bs);(pid id);(print vs);
              (case dc
                 of [] => legoprint dt
                  | _  => ((print "\n");
                           (vooprint1 false (ind+1) (rev dc,dt))));
              (vooprint1 flag ind (Rev rt,tail))) end
           | (ref (Bd {kind=Dom (id,(sc,st)),bd=(bv,_,_,_),...}))::rt =>
             let val (bs,vs) = bvBits bv in
             ((indent ind);(print bs);(pid id);(print vs);
              (case rt
                 of [] => ((if flag then print "=> " else ());
                           (legoprint tail))
                  | _  => ((print "\n");
                           (vooprint1 flag (ind+1) (Rev rt,tail))));
              (vooprint1 false ind (rev sc,st))) end
           | _ => failwith "bad bad voodoo!"
in  fun vooprintstate (ctxt,tail) = vooprint1 true 0 (rev ctxt,tail)
end

local
    fun pa2 aa vv (App ((f,a),v)) = pa2 (a@aa) (v@vv) f
      | pa2 aa vv f = (f,aa,vv)
in
    fun parseApp t = pa2 [] [] t
end

(* Given some rewriting function (int -> cnstr -> cnstr modif),
   >>> applies it to a whole state, including the
   cached binder_data stuff; if the rewriting function is type-safe,
   everything should be ok *)

infix >>> (* voorewrite state *)

fun mang>>>(ctxt,tail) =
    let fun zob x = mang>>x
        fun boof ctxt = ((vooctxtrec
            {hitBot = fn _ => (),
             hitDom = fn (id,(vc,vt)) => fn b => fn _ => fn rect =>
                      let val (bv,nam,v,t) = ref_bd b
                          val v' = if bv=HoleBV
                                   then case v
                                          of Var (x,t) => Var (x,zob t)
                                           | _ => zob v
                                   else zob v
                          val _ = (b<!(Dom (id,(boof vc,zob vt))))<:
                                      (bv,nam,v',zob t)
                      in  rect ()
                      end,
             hitVoo = fn (id,(dc,dt)) => fn b => fn _ => fn rect =>
                      let val (bv,nam,v,t) = ref_bd b
                          val v' = if bv=HoleBV
                                   then case v
                                          of Var (x,t) => Var (x,zob t)
                                           | _ => zob v
                                   else zob v
                          val _ = (b<!(Voo (id,(boof dc,zob dt))))<:
                                      (bv,nam,v',zob t)
                      in  rect ()
                      end} ctxt);ctxt)
    in  (boof ctxt,zob tail)
    end

(* only rename in scope *)
fun vooRename scheme (S as (C,T)) =
    let fun $(id as (s,i)) =
           (assoc id scheme
            handle Assoc =>
            let val (s',j) = assoc (s,0) scheme
            in  (s',i+j)
            end
            handle Assoc => id)
        fun boof ctxt = vooctxtrec
            {hitBot = fn _ => (),
             hitDom = fn (id,S) => fn b => fn _ => fn rect =>
                      ( (rect ());
                        (b<!(Dom ($id,S)));
                        () ),
             hitVoo = fn (id,S) => fn b => fn _ => fn rect =>
                      ( (rect ());
                        (b<!(Voo ($id,S)));
                        () )} ctxt
    in  ((boof C);S)
    end

local
    fun copyBdsOnly mang =
        let fun doCtxt al = vooctxtrec
               {hitBot = fn C => (C,al),
                hitDom = fn (id,(VC,VT)) => fn b => fn _ => fn rect =>
                         let val (C,al) = rect ()
                             val (VC',al) = doCtxt al VC
                             val b' = (!!b) <! (Dom (mang id,(VC',VT)))
                         in  (b'::C,(b,Ref b')::al)
                         end,
                hitVoo = fn (id,(DC,DT)) => fn b => fn _ => fn rect =>
                         let val (C,al) = rect ()
                             val (DC',al) = doCtxt al DC
                             val b' = (!!b) <! (Voo (mang id,(DC',DT)))
                         in  (b'::C,(b,Ref b')::al)
                         end}
        in  doCtxt []
        end
    fun rassoc b =
        let fun ra2 [] = raise Assoc
              | ra2 ((b',x)::t) = if sameRef b b' then x else ra2 t
        in  ra2
        end
in  fun vooHitRef al _ (Ref b) = (Mod (rassoc b al)
                               handle Assoc => UMod)
      | vooHitRef _ _ _ = UMod
    fun vooMangCopy mang (ctxt,tail) =
        let val (ctxt',al) = copyBdsOnly mang ctxt
        in  (vooHitRef al)>>>(ctxt',tail)
        end
    val vooCopy = vooMangCopy iota
end

infix %>>

fun al%>>t = (vooHitRef al)>>t

infix %>>>

fun al%>>>S = (vooHitRef al)>>>S

fun safeNumber (ctxt,_) s = vooctxtrec
    {hitBot = fn _ => fn i => i,
     hitDom = fn ((r,h),(vc,_)) => fn _ => fn _ => fn rect => fn i =>
              rect () (safeNumber (vc,Prop) s 
                       (if ((s=r) orelse (s="")) andalso (h>=i)
                        then h+1 else i)),
     hitVoo = fn ((r,h),(dc,_)) => fn _ => fn _ => fn rect => fn i =>
              rect () (safeNumber (dc,Prop) s
                       (if ((s=r) orelse (s="")) andalso (h>=i)
                        then h+1 else i))}
    ctxt

fun safeNumberScope (ctxt,_) s = vooctxtrec
    {hitBot = fn _ => fn i => i,
     hitDom = fn ((r,h),_) => fn _ => fn _ => fn rect => rect (),
     hitVoo = fn ((r,h),_) => fn _ => fn _ => fn rect => fn i =>
              rect () (if ((s=r) orelse (s="")) andalso (h>=i)
                       then h+1 else i)}
    ctxt

(* vooSolve is the main means by which we make progress; it takes
   an id and a trick looking like ([?]..[?][:]..[:],blah)
      together with the state to be modified (destructively, ha ha)
   and replaces the binder for id with [?]..[?],
   then replaces V-id everywhere with ([:]..[:]blah) collapsed
        or copied as appropriate;
   finally, the whole thing has beta and iota redexes removed *)

local
    fun varHole _ (Var ((_,x as Ref _),_)) = Mod x
      | varHole _ _ = UMod
    fun fixit sbst = map (fn (n,c) => (n,varHole>>c)) sbst
in
    infix $>>
    fun s $>> t = sub (fixit s) t

    infix $>>>
    fun s $>>> (C,T) =
        let val s = fixit s
            val (C',zap) = vooctxtrec
               {hitBot = fn b => (b,[]),
                hitDom = fn _ => fn b => fn _ => fn rect =>
                         ((cons b)**iota) (rect ()),
                hitVoo = fn _ => fn b => fn _ => fn rect =>
                        (case ref_bd b
                           of ((Hole,Def),_,Var ((n,_),_),_) =>
                              (iota**(cons (b,assoc n s))
                               handle Assoc => (cons b)**iota)
                            | _ => (cons b)**iota) (rect ())} C
        in  zap%>>>(C',T)  (* relies on zap doing whole subst---no new vars *)
        end

    val varHole = varHole
    fun varFix t = varHole>>t
    val vooWhnf = varFix o whnf
end

fun vooDnf _ c = Mod (UMdnf c)

val globalTrustMe = ref true

fun vooSolve trustMe id (trickS as (trickP,trickT)) (stateP,stateT) =
    let (* first find id in state *)
        val ((below,here),above) = vooctxtrec
            {hitBot = voobottom,
             hitDom = fn _ => fn b => fn _ => fn rect =>
                      (iota**(cons b)) (rect ()),
             hitVoo = fn (jd,_) => fn b => fn t => fn rect =>
                      if id=jd then ((t,b),[])
                      else (iota**(cons b)) (rect ())} stateP
        val (holes,ldas,rest) = vooctxtrec
            {hitBot = fn _ => ([],[],[]),
             hitDom = fn _ => fn b => fn _ => fn rect =>
                      let val (l,m,n) = rect ()
                      in  (l,m,b::n)
                      end,
             hitVoo = fn _ => fn b => fn _ => fn rect =>
                      let val (l,m,n) = rect ()
                      in  case #1 (ref_bd b)
                            of (Hole,_) => if n=[] andalso m=[]
                                              then (b::l,[],[])
                                              else (l,m,b::n)
                             | (Let,_) => if n=[] andalso m=[]
                                             then (b::l,[],[])
                                             else (l,m,b::n)
                             | (Lda,_) => if n=[]
                                          then (l,b::m,[])
                                          else (l,m,b::n)
                             | _ => (l,m,b::n)
                      end} trickP
        val realTrick as (realP,realT) = (rest@ldas,trickT)
        val trick = $!realTrick
        (* check solution well-typed *)
        val _ = if trustMe orelse (!globalTrustMe) (* possible speedup? *)
                then ()                (* really want a typecheck fn *)
                else case par_unif [] (type_of_constr trick) (ref_typ here)
                                     (* must be this way round: universes *)
                     of SOME _ => ()
                      | NONE => failwith "type error in solution"
        val notchUpBy = safeNumber trickS "" 1
        fun notchUp (s,i) = (s,i+notchUpBy)
        val rLdas = rev ldas
        exception noZap
        fun zap flag ll [] _ al =
            (vooHitRef al)>>>((if flag then vooCopy else iota)
                              (rest@(unrev ll),realT))
          | zap flag (Rev (lh::lt)) (ah::at) (vh::vt) al =
            zap flag (Rev lt) at vt ((lh,ah)::al)
          | zap flag _ _ _ _ = raise noZap
        fun tip flag t =
            let  val (f,aa,vv) = parseApp t
            in   if isit id f
                 then zap flag rLdas aa vv []
                      handle noZap => ([],MkApp ((trick,aa),vv))
                 else ([],t)
            end
        fun doTips flag (C,T) = (* flag true if we need to copy trick *)
            let val (TC,TT) = tip flag T
                val CC = doCtxt C
            in  (TC@CC,TT)
            end
        and doCtxt C = vooctxtrec
            {hitBot = iota,
             hitDom = fn (id,V) => fn b => fn _ => fn rect =>
                      (b<!(Dom (id,doTips true V)))::(rect ()),
             hitVoo = fn (id,D) => fn b => fn _ => fn rect =>
                      (b<!(Voo (id,doTips true D)))::(rect ())} C
        val (AC,AT) = varHole>>>(vooDnf>>>((vooHitRef [(here,trick)])>>>
                                 (doTips false (above,stateT))))
    in  (AC@holes@below,AT)
    end

infix \ (* vooSolve *)

fun id\trick = vooSolve false id trick

fun voosynth (S as (_,tail)) =
    let val (f,a,_) = parseApp tail
        fun infer sbst (Vf,Bind ((Pi,v),_,dom,rng)) (Va::at) =
            let val Va = sub sbst Va
                val Ta = type_of_constr Va
                val sbst =
                    case par_unif sbst Ta dom
                      of SOME s => s
                       | NONE => raise Error.error (Error.APPLNTYPE,NONE,
					            [Vf,dnf dom,Va,dnf Ta])
                val pv = case v of Vis => ShowNorm | _ => ShowForce
                val Vf = sub sbst (MkApp((Vf,[Va]),[pv]))
                val Tf = whnf (sub sbst (subst1 Va rng))
            in  infer sbst (Vf,Tf) at
            end
          | infer sbst (Vf,Tf) [] = sbst $>>> S
          | infer _ (Vf,Tf) _ =
            raise Error.error (Error.APPLNNFUN,NONE,[Vf, dnf Tf])
    in  infer [] (f,whnf (type_of_constr f)) a
    end

fun synthApp f a v =
    let val ((trick,_),sbst) = Machine.Apply [] global_pvp v
                               (f,type_of_constr f) (a,type_of_constr a)
    in  sub sbst trick
    end

fun vooetastate (S as ([],tail)) = S
  | vooetastate (S as (b::t,tail)) =
    case !b
      of Bd {kind=Voo _,bd=((Lda,lv),_,_,_),...} =>
        (let val (f,a,v) = parseApp tail
             val (al,ab) = sep_last a
             val (vl,vb) = sep_last v
             val bobbit = MkApp ((f,ab),vb)
             val visChk = case (lv,vl)
                            of (Vis,ShowNorm) => true
                             | (Hid,NoShow) => true
                             | (Hid,ShowForce) => true
                             | _ => false
         in  case al
               of Ref b' =>
                  if visChk andalso sameRef b b'
                            andalso (not (depends b bobbit))
                  then vooetastate (t,bobbit)
                  else S
                | _ => S
         end
         handle Failure _ => S)
       | _ => S

fun vooeta t = $!(on (start t) [introall iota "eta" 1,
                                vooetastate])

fun voofloat (id,bv,nam,dom) (ctxt,tail) =
    vooin id (ctxt,Bind (bv,nam,dom,tail))

fun vootwist id (S as (ctxt,_)) = vooctxtrec
    {hitBot = voobottom,
     hitDom = fn (jd,_) => fn _ => fn _ => fn _ =>
              if id=jd then S
              else vootwist id (domvoo jd S),
     hitVoo = voocontinue} ctxt

fun ArgsAndVis warp ctxt = vooctxtrec
    {hitBot = fn _ => fn av => av,
     hitDom = fn _ => fn _ => fn _=> fn _ => fn av => av,
     hitVoo = fn _ => fn b => fn _ => fn rect => fn av =>
              rect () (((cons (warp (Ref b)))**(cons (prVis (ref_vis b)))) av)}
    ctxt ([],[])

fun voobinrev b (Rev r,t) = voobin b (r,t)
and voobin b (l,t) =
    (depends b t)
    orelse
    (exists (voobinb b) l)
and voobinb b B = case ref_kind B
                    of Voo (_,D) => voobin b D
                     | Dom (_,V) => voobin b V
                     | _ => false

fun vooshove b (ctxt,tail) =
    let val ctxt' = vooctxtrec
                    {hitBot = fn _ => [b],
                     hitDom = fn _ => fn d => fn t => fn _ => b::d::t,
                     hitVoo = fn _ => fn v => fn t => fn rect =>
                              if (ref_bind v)<>Lda
                              then if voobinb v b (* dep check *)
                                   then b::v::t
                                   else v::(rect ())
                              else b::v::t} ctxt
    in  (ctxt',tail)
    end

val voodep1l = voofold [] union
               (fn ref (Bd {kind=Voo (id,_),...}) => [id]
                 | _ => [])

fun vooty id S = case ref_kind (fetch S id)
                   of Voo (_,D) => D
                    | _ => raise missing_voodoo

val vooctxtdepfilter = vooctxtrec
    {hitBot = fn _ => fn _ => ([],[]),
     hitDom = voocontinue,
     hitVoo = fn _ => fn b => fn _ => fn rect => fn l =>
              if exists (depends b) l
              then ((cons b)**iota) (rect () ((ref_typ b)::l))
              else (iota**(cons b)) (rect () l)}

fun voodep term S =
    let fun search idsDone [] = idsDone
          | search idsDone (nextId::idsLeft) =
            let val moreIds = voodep1l ($!(vooty nextId S))
                              handle missing_voodoo => []
                val (_,extra) =
                    filter (fn id => (member id idsDone) orelse
                                     (member id idsLeft)) moreIds
            in search (nextId::idsDone) (moreIds@idsLeft)
            end
    in  search [] (voodep1l term)
    end

fun voomerge x y =
    let fun vsp2 x [] = (x,b42)
          | vsp2 x (b::t) =
            let val (x,id) = vsp2 x t
                val id' = bid b
                fun shove [] = [b]
                  | shove (h::t) =
                    if (id=(bid h)) orelse (voobinb h b)
                    then b::h::t else h::(shove t)
            in  (shove x,id')
            end
    in  #1 (vsp2 x y)
    end

fun vootopsort [] = []
  | vootopsort (h::t) = voomerge (vootopsort t) [h]

fun voohead (Bind (_,_,_,r)) = voohead r
  | voohead (App ((f,_),_))  = voohead f
  | voohead x                = x

fun vooattack goalId solId (ctxt,tail) = voodom goalId (vooctxtrec
    {hitBot = voobottom,
     hitDom = voocontinue,
     hitVoo = fn (id,D) => fn b => fn t => fn rect =>
              if id=goalId
              then
              let val bd as (_,nam,dom,ran) = ref_bd b
                  val sb = (!!b)<!(Voo (solId,D))
                  val _ = (b<!(Voo (id,([sb],Ref sb))))
                            <:((Let,Def),nam,dom,ran)
              in  b::t
              end
              else b::(rect ())} ctxt,tail)

fun ldify b = case ref_bd b
                of ((_,v),nam,dom,ran) => b<:((Lda,v),nam,dom,ran)

fun pihole b = case ref_bd b
                 of (_,nam,dom,ran) => b<:(HoleBV,nam,hole_pvp b dom,dom)

fun safepihole b =
    case ref_bd b
      of ((Pi,_),nam,dom,ran) => b<:(HoleBV,nam,hole_pvp b dom,dom)
       | _ => b

fun holepiv b = case ref_bd b
                  of (_,nam,_,ty) => b<:((Pi,Vis),nam,ty,type_of_constr ty)

fun holesigv b = let val ty = ref_typ b
                     val bv = #1 (ref_bd b)
                     val b = b<:((Sig,Vis),ref_nam b,ty,type_of_constr ty)
                 in  case bv
                       of (Let,Def) => b <! (Voo (bid b,([],ty)))
                        | _ => b
                 end

fun holeldav b = case ref_bd b
                   of (_,nam,_,ty) => b<:((Lda,Vis),nam,ty,type_of_constr ty)

fun letpiv b = case ref_bd b
                 of (_,nam,_,ty) => (b<:((Pi,Vis),nam,ty,type_of_constr ty))
                                     <!(Voo (bid b,([],ty)))

fun pify b = case ref_bd b
               of ((_,v),nam,dom,ran) => b<:((Pi,v),nam,dom,ran)

fun sigify b = case ref_bd b
                 of ((_,v),nam,dom,ran) => b<:((Sig,v),nam,dom,ran)

fun anon b = case ref_bd b
               of (bv,_,dom,ran) => b<:(bv,"",dom,ran)

fun vise b = case ref_bd b
               of ((s,_),nam,dom,ran) => b<:((s,Vis),nam,dom,ran)

fun hide b = case ref_bd b
               of ((s,_),nam,dom,ran) => b<:((s,Hid),nam,dom,ran)

fun mkBnd b = b <! Bnd

fun vNam s b = case ref_kind b
                 of Voo ((_,i),D) => b<!(Voo ((s,i),D))
                  | Dom ((_,i),V) => b<!(Dom ((s,i),V))
                  | _ => b

fun bmem b = vooctxtrec
            {hitBot = const false, hitDom = voocontinue,
             hitVoo = fn _ => fn b' => fn _ => fn rect =>
                      (sameRef b b') orelse (rect ())}

fun newid id b = case ref_kind b
                   of Voo (_,D) => b<!(Voo (id,D))
                    | Dom (_,V) => b<!(Dom (id,V))
                    | _ => b

fun alBind al b =
    let val mang = vooHitRef al
        val bd' = case ref_bd b
                    of (bv,nam,dom,ran) => (bv,nam,mang>>dom,mang>>ran)
        val kind' = case ref_kind b
                      of Voo (id,D) => Voo (id,mang>>>D)
                       | Dom (id,V) => Dom (id,mang>>>V)
                       | _ => failwith "rewriting a bad binder"
        val b = (b<:bd')<!kind'
    in  b
    end

fun copyCtxt mang = vooctxtrec
    {hitBot = fn _ => ([],([],[])),
     hitDom = fn _ => fn _ => fn _ => fn _ => ([],([],[])),
     hitVoo = fn (id,D) => fn b => fn _ => fn rect =>
              let val (C,(zap,paz)) = rect ()
                  val b' = mang (alBind zap ((!!b)<!(Voo (id,vooCopy D))))
              in  (b'::C,((b,Ref b')::zap,(b',Ref b)::paz))
              end}

fun voofilter p = vooctxtrec
    {hitBot = fn _ => ([],[]), hitDom = voocontinue,
     hitVoo = fn _ => fn b => fn _ => fn rect =>
              (if p b then (cons b)**iota else iota**(cons b)) (rect ())}

(* this moves a hole over a bunch of pis (now does check they really are),
   turning them into ldas *)
fun vooGenIntro bInit bUpd bTest id S = case S ?! id of (dc,dt) =>
    let val (newC,rest,_) = vooctxtrec
            {hitBot = fn _ => ([],[],bInit), hitDom = voocontinue,
             hitVoo = fn _ => fn b => fn _ => fn rect =>
                      let val (newC,rest,bag) = rect ()
                      in  case (rest,ref_bind b)
                            of   ([],Pi)  =>
                               if bTest b bag then (newC,b::rest,bag)
                               else ((ldify b)::newC,[],bUpd b bag)
                             |   ([],Let) =>
                               if (bTest b bag) orelse (ref_vis b)<>Def
                               then (newC,b::rest,bag)
                               else (b::newC,[],bUpd b bag)
                             |      _     => (newC,b::rest,bag)
                      end} dc
        val b' = noo (HoleBV,"") id (rest,dt)
        val trick = (b'::newC,Ref b')
    in  (id\trick) S
    end

fun vooBeforeDom b' (C,T) =
    let val C' = vooctxtrec {
                  hitBot = fn _ => [b'],
                  hitDom = fn _ => fn b => fn t => fn _ => b::b'::t,
                  hitVoo = fn _ => fn b => fn _ => fn rect => b::(rect ())
                 } C
    in  (C',T)
    end

val vooIntroTac = vooGenIntro () (const iota) (const (const false))

fun vooIntroNTac n = vooGenIntro n (const (fn n => n-1)) (const (fn n => n=0))

fun vooIntroUpToTac jd = vooGenIntro false (fn b => fn _ => (bid b)=jd)
                                     (const iota)

fun vooSplitSigHole id S =
    let val b = fetch S id
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
                              let val ot = $!D
                                  val b = b<:(HoleBV,"",hole_pvp b ot,$!D)
                              in  (b::holes,[])
                              end
                            | _ => (holes,b::spares)
                     end} bC
        val nh = noo (HoleBV,"") id (spareList,bT)
        fun mkT [] l = l
          | mkT (h::t) l = mkT t ((Ref h)::l)
        val trick = MkTuple (oldTy,mkT holeList [Ref nh])
    in  (id \ (nh::holeList,trick)) S
    end

exception bluePlasticHammerWaaaaah

fun vooRefineTac gid holeName byThis S =
    let val targ = case ref_kind (fetch S gid)
                     of Voo (_,D) => $!D
                      | _ => failwith "no goal to solve"
        val Ty = type_of_constr byThis
        val hi = safeNumber S holeName 1
        fun refine i holes tm ty =
            case par_unif [] ty targ
              of SOME sbst => (sbst,(holes,tm))
               | NONE => case whnf ty
                           of Bind ((Pi,v),nam,dom,ran) =>
                              let val nh = noo (HoleBV,"") (holeName,i) ([],dom)
                                  val guess = Ref nh
                                  val ran = subst1 guess ran
                                  val tm = MkApp ((tm,[guess]),[prVis v])
                              in  refine (i+1) (nh::holes) tm ran
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
        val trick = sbst$>>>trick (* seems necessary *)
    in  sbst$>>>((gid \ trick) S)
    end

fun vooRefineId gid holeName id S =
    vooRefineTac gid holeName (vid S id) S

fun vooAssumption (S as (ctxt,_)) =
    let val sbst = vooctxtrec
           {hitBot = fn _ => iota, hitDom = voocontinue,
            hitVoo = fn _ => fn b => fn t => fn rect => fn sbst =>
                     case ref_bd b
                       of ((Hole,Def),_,Var ((n,_),_),ty) =>
                         (((assoc n sbst); (* already got it ? *)
                           (rect () sbst))
                          handle Assoc => rect ()
                          let val ty = sbst$>>ty
                          in  vooctxtrec
                             {hitBot = fn _ => sbst,
                              hitDom = voocontinue,
                              hitVoo = fn _ => fn b => fn _ => fn rect =>
                                       case par_unif sbst
                                            (sbst$>>(ref_typ b)) ty
                                         of SOME s => compose sub [(n,Ref b)] s
                                          | NONE => rect ()} t
                          end)
                        | _ => rect () sbst} ctxt []
    in  sbst$>>>S
    end

fun vooBindSearch (C,_) test = vooctxtrec
   {hitBot = fn _ => false,
    hitDom = fn (_,V) => fn b => fn _ => fn rect =>
             (test b) orelse (vooBindSearch V test) orelse (rect ()),
    hitVoo = fn (_,V) => fn b => fn _ => fn rect =>
             (test b) orelse (vooBindSearch V test) orelse (rect ())} C

fun voosubdef id S =
    case !(fetch S id)
      of Bd {kind=Voo (_,D),bd=((Let,Def),_,_,_),...} => (id\D) S
       | _ => raise missing_voodoo

fun vookcatta id S = on S [domvoo id,voosubdef id]

fun vooFlattenReds id S =
    let val (ctxt,_) = voodom id S
        val xi = safeNumberScope (ctxt,Prop) "x" 1
        val (_,redL,ctxt) = vooctxtrec
            {hitBot = fn b => (xi,[],b),
             hitDom = fn _ => fn b => fn t => fn _ => (xi,[],b::t),
             hitVoo = fn (_,D as (dc,_)) => fn _ => fn _ => fn rect =>
                      let val (xi,redL,ctxt) = rect ()
                          val (ctxt,red) = introall iota "x" xi (ctxt,$!D)
                          val xi=xi+(length dc)
                          val red = case red
                                    of CnLst [red as LabVT (RedPr,lhs,rhs)] =>
                                       LabVT (RedPr,lhs,rhs)
                                              (* better here than never *)
                                     | _ => failwith "not a reduction!"
                      in  (xi,redL@[red],ctxt)
                      end} ctxt
    in  domvoo id (ctxt,CnLst redL)
    end

fun makeRedVT V =
    let fun v2t (Bind ((Lda,v),nam,dom,rng)) =
                 Bind ((Pi,v),nam,dom,v2t rng)
          | v2t _ = Bot
    in  (V,v2t V)
    end

fun vooFoldRew unEx (ldas,ex) =
    let exception noReds
        val (oC,(zap,_)) = copyCtxt pihole ldas
        val (aa,vv) = ArgsAndVis (fn t => zap%>>t) ldas
        val oL = MkApp ((unEx,aa),vv)
        val oR = zap%>>ex
        val (oF,oAA,oVV) = parseApp oR
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

fun vooGoal (tyid::defid::what) gid (c,t) =
    let val S = (vooctxtrec
                {hitBot = fn _ => [],
                 hitVoo = fn _ => fn b => fn _ => fn rect => b::(rect ()),
                 hitDom = fn _ => fn b => fn _ => fn rect => b::(rect ())} c,t)
        val Scopy = vooCopy S
        val typ = noo ((Let,Def),#1 tyid) tyid Scopy
        val goal = noo (HoleBV,#1 gid) gid S
        val def = noo ((Let,Def),#1 defid) defid ([],Ref goal)
        val soFar = def::goal::typ::VooBase::(getNamespace())
    in  case what
          of [] => (soFar,Prop)
           | (redid::_) =>
        let val red1 = ((Sig,VBot),"",Bot,Bot):!
                       (Voo (("red",safeNumber (c,t) "red" 1),([],
                              CnLst [LabVT (RedPr,Ref def,Ref goal)])))
            val reds = ((Sig,VBot),#1 redid,Bot,Bot):!
                        (Voo (redid,([red1],Prop)))
        in  (reds::soFar,Prop)
        end
    end
  | vooGoal _ _ _ = failwith "bad attempt to start goal"

fun vooAddReductions redV =
    let val redVT = makeRedVT redV
        val _ = legoprint redV
        val _ = SaveReductGbl redVT
        val _ = message "compiling reductions"
        val _ = add_reductions redV
    in  ()
    end

fun vooQED [tyid,defid] tag S =
    let val realCtxt = getNamespace()
    in  let
        val theType = case ref_kind (fetch S tyid)
                        of Voo (_,(dc,dt)) =>
                           stop (dc@(VooBase::realCtxt),dt)
                         | _ => failwith "couldn't get type"
        val theTerm = case ref_kind (fetch S defid)
                        of Voo (_,(dc,dt)) =>
                           stop (dc@(VooBase::realCtxt),dt)
                         | _ => failwith "couldn't get term"
        val _ = case par_unif [] (type_of_constr theTerm) theType
                  of NONE => failwith "proof fails to typecheck"
                   | _ => ()
        val nicePair = (theTerm,theType)
        val realName = mkNameGbl (tagName tag)
        val _ = print ("Trying to add "^realName^"\n")
    in  if (not (activeProofState()))
        then ( (extendCxtGbl (GenTag tag) (Let,Def) (UnFroz,Global)
                [] realName nicePair);
               (fEval (Ref_c realName)) )
        else failwith "can't add this definition in proofstate"
        end
        handle x => ((putNamespace realCtxt);raise x)
    end
  | vooQED [tyid,defid,redid] tag S =
    let val realCtxt = getNamespace()
    in  let
        val nicePair as (tm,_) = vooQED [tyid,defid] tag S
        val refNam = case tm of (Ref b) => ref_nam b
                              | _ => failwith "disaster"
        val _ = Freeze [refNam]
        val S' = on S [defid \ ([],tm),
                       vooFlattenReds redid]
        val S'' as (ctxt,tail) = voodom redid S'
        val _ = Unfreeze [refNam]
        val _ = case tail
                  of CnLst l =>
                     map (fn LabVT (RedPr,lhs,rhs) =>
                            (case par_unif [] lhs rhs
                               of NONE => failwith "bad derived reduction"
                                | SOME _ => ())
                           | _ => failwith "bad reduction syntax") l
                   | _ => failwith "bad reduction syntax"
        val S' = domvoo redid S''
        val redV = case ref_kind (fetch S' redid)
                     of Voo (_,(dc,dt)) =>
                        stop (dc@(VooBase::(getNamespace())),dt)
                      | _ => failwith "bad reduction syntax"
        val _ = (print "with reductions\n")
        val _ = vooAddReductions redV
        val _ = Freeze [refNam]
    in  nicePair
        end
        handle x => ((putNamespace realCtxt);raise x)
    end
  | vooQED _ _ _ = failwith "bad attempt at definition"

fun vooQEDlist [] S = ()
  | vooQEDlist info S =
    let val realCtxt = getNamespace()
    in
    let val (allIn,frz) =
             foldr (fn (tyid::defid::tail,tag) => (fn (S,ff) =>
                        let val (tm,_) = vooQED [tyid,defid] tag S
                            val S = (defid \ ([],tm)) S
                        in  case tail
                              of [] => (S,ff)
                               | redid::_ => (vooFlattenReds redid S,
                                              (ref_nam (unRef tm))::ff)
                        end)
                      | _ => failwith "bad attempt at definition")
                    (S,[]) info
        val _ = map
                (fn ([_,_,redid],tag) =>
                 let val (C,T) = allIn ?! redid
                     val _ = case T
                               of CnLst l =>
                                  map (fn LabVT (RedPr,lhs,rhs) =>
                                       (case par_unif [] lhs rhs
                                          of NONE =>
                                             failwith "bad derived reduction"
                                           | SOME _ => ())
                                     | _ => failwith "bad reduction syntax") l
                                | _ => failwith "bad reduction syntax"
                     val redV = $!(C,T)
                     val _ = vooAddReductions redV
                 in  ()
                 end
                  | _ => ()) info
        val _ = Freeze frz
    in  ()
    end
    handle x => ((putNamespace realCtxt);raise x)
    end

type voodemon = string list -> cnstr * cnstr

val vooDemons = ref ([]:voodemon list)

fun theVooDemon tag =
    let fun tryem [] = raise RequireFailure
          | tryem (h::t) = (h tag,false)
            handle RequireFailure => tryem t
    in  tryem (!vooDemons)
    end

fun addVooDemon D =
    vooDemons := D::(!vooDemons)

fun vooSubSequence s tac (S as (ctxt,tail)) = vooctxtrec
    {hitBot = fn _ => S,hitDom = voocontinue,
     hitVoo = fn ((t,i),_) => fn _ => fn _ => fn rect =>
              if s=t then tac i (rect ()) else rect ()} ctxt

fun vooSubSubSequence s ss tac S =
   (let val C = case ref_kind (fetch S s)
                  of Voo (_,(C,_)) => C
                   | _ => raise missing_voodoo
    in  let
        fun doit [] = S
          | doit (h::t) =
            let val S = doit t
                val hi = bid h
            in  if (#1 hi)=ss then tac s hi S
                else S
            end
    in  doit C
    end end
    handle missing_voodoo => S)

fun vooForLoopTac tac i j S =
    if i>j then S
    else vooForLoopTac tac (i+1) j (tac i S)

fun vooStealGoal l g =
    vooGoal l g (start (#2 (Synt.goaln (~9999))))

fun vooLegoRefine l (S as (ctxt,_)) =
    let val (typ,trick) = case l of [x,y] => (x,y)
                                  | _ => failwith "can't refine like that"
        val trickTail = ref_val (fetch S trick)
        val (holesBetween,_) = vooctxtrec
            {hitBot = voobottom, hitDom = voocontinue,
             hitVoo = fn (id,_) => fn b => fn _ => fn rect =>
             if id=typ then ([],true)
             else if id=trick then (iota**not) (rect ())
             else let val (l,f) = rect ()
                  in  if f then (b::l,true) else (l,false)
                  end} ctxt
        val (ldas,(zap,_)) = copyCtxt (ldify o vise) holesBetween
        val theThang = $!(vooetastate (ldas,zap%>>trickTail))
        val _ = voofold () (fn VooDont => failwith "voodoo leak"
                             | Voo _ => failwith "voodoo leak"
                             | Dom _ => failwith "voodoo leak"
                             | _ => iota) ref_kind theThang
    in ((Namespace.pushHist ());
        (message "You don't want to see the term I'm refining by...");
        (Toplevel.RefineTac_c (~9999) 0 (unEval theThang) (!Toplevel.AutoTac));
        (Toplevel.Pr()))
    end

(**)
val _ = AddRequireDemon theVooDemon
(**)
