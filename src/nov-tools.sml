fun hasName s b = (fst (bid b))=s

fun listHoles ts hs = foldr listHole hs ts
and listHole (Var ((h,_),_)) = cons h 
  | listHole (Bind (_,_,d,r)) = (listHole d) o (listHole r)
  | listHole (App ((f,aa),_)) = (listHole f) o (listHoles aa)
  | listHole (CnLst aa) = listHoles aa
  | listHole (LabVT (_,l,r)) = (listHole l) o (listHole r)
  | listHole (Tuple (a,aa)) = (listHole a) o (listHoles aa)
  | listHole (Proj (_,t)) = listHole t
  | listHole _ = iota

fun chop [] aa vv = (([],[]),(aa,vv))
  | chop (_::ts) (a::aa) (v::vv) = (((cons a)**(cons v))**iota)
                                   (chop ts aa vv)
  | chop _ _ _ = failwith "not enough to chop"
    
fun rassoc b =
    let fun ra2 [] = raise Assoc
          | ra2 ((b',x)::t) = if sameRef b b' then x else ra2 t
    in  ra2
    end

fun claimHolesSolveGoals gns nxtMang (HC,GT) =
    let (*val _ = vooprintstate (HC,GT)*)
        fun claimRew [] = ([],[],[])
          | claimRew (b::bs) =
            let val (al,clms,frzs) = claimRew bs
                val clmTy = al %>> ($! (bCT b))
            in  case bid b
                  of ("lego",g) =>
                     let val _ = Toplevel.Refine g 0 (unEval clmTy)
                     in (al,clms,frzs)
                     end
                   | _ =>
           (case #1 (ref_bd b)
              of (Let,Def) =>
            let val v = unEval (al %>> ($! (bCT b)))
                val t = unEval (al %>> (ref_TYP b))
                val _ = Top.EvalCxt
                        [(Let,Def,(UnFroz,Local),ref_deps b,[ref_nam b],
                              Cast_c (v,t))]
                val b' = hd (tl (fst (start Prop)))
                val frzs' = case !(ref_frz b) of Froz => (ref_nam b')::frzs
                                               | _ => frzs
            in ((b,Ref b')::al,clms,frzs')
            end
               | _ =>
            let val _ = legoprint clmTy
                val _ = Toplevel.Claim (unEval clmTy)
                val clmNm = fst (Synt.goal_rel (true,0))
                val clmTm = Var ((clmNm,Bot),clmTy)
            in  ((b,clmTm)::al,(clmNm,clmTy,bid b)::clms,frzs)
            end) end
        val tac = tactic_wrapper (fn _ => let
        val (al,clms,frzs) = claimRew HC
        val _ = case al %>> GT
                  of App ((_,aa),_) =>
                     let fun sol (gn::gns) (gs::gss) =
                             ((legoprint gs);
                              (Toplevel.Refine gn 0 (unEval gs));(sol gns gss))
                           | sol _ _ = ()
                     in  sol gns aa
                     end
                   | _ => ()
        fun nexts [] = ()
          | nexts (g::gs) = ((Toplevel.Next g);(nexts gs))
        val _ = Namespace.Freeze frzs
        val _ = nexts (nxtMang clms)
    in  () end) in tac ()
    end

fun dependsList bs =
    voofold false (fn p => fn q => p orelse q)
            (fn b => exists (sameRef b) bs)

fun vooNonDepCut CC BB =
    let fun vndc [] = (([],[]),BB)
          | vndc (b::bs) =
            let val ((CCb,CCa),BB) = vndc bs
            in  if dependsList BB (ref_typ b)
                then ((CCb,b::CCa),b::BB)
                else ((b::CCb,CCa),BB)
            end
    in  fst (vndc CC)
    end

local
fun vooDC [] Ts CC = CC ([],[])
  | vooDC (b::bs) Ts CC
    = if depends b (CnLst Ts)
      then vooDC bs ((ref_typ b)::Ts) (((cons b)**iota) o CC)
      else vooDC bs Ts ((iota**(cons b)) o CC)
in  fun vooDepCut C Ts = vooDC C Ts iota
end

fun isTypeFam (Bind ((Pi,_),_,_,r)) = isTypeFam r
  | isTypeFam Prop = true
  | isTypeFam (Type _) = true
  | isTypeFam _ = false

fun isBFam b (Bind ((Pi,_),_,_,r)) = isBFam b r
  | isBFam b (App ((f,_),_)) = isBFam b f
  | isBFam b (Ref b') = sameRef b b'
  | isBFam _ _ = false

fun Cfoldr f x = vooctxtrec {
      hitBot = fn _ => x,
      hitDom = fn _ => fn _ => fn _ => fn _ => x,
      hitVoo = fn _ => fn b => fn _ => fn rect => f b (rect ())}

fun Cfoldl f x C = vooctxtrec {
      hitBot = fn _ => iota,
      hitDom = fn _ => fn _ => fn _ => fn _ => iota,
      hitVoo = fn _ => fn b => fn _ => fn rect => fn x => rect () (f x b)} C x

fun wrapUnify s t NONE = NONE
  | wrapUnify s t (SOME sbst) = par_unif sbst s t

fun Cfilter p = Cfoldr (fn b => fn (ys,ns) =>
                        if p b then (b::ys,ns) else (ys,b::ns))
                       ([],[])

fun isLocal C b = Cfoldr (fn b' => fn p => p orelse sameRef b b') false C
                          
 (******
Conor's test for being a constructor is a little dodgy. Check that the var
is a function with return type an instance of some family fam; then check
that var occurs in the deps of fam. It's far from perfect and it could be
fooled quite easily. Note, this means that // Eqr must be added to the
declaration of Eq in lib_eq.

A better solution would involve really marking constructors as constructors,
but that requires more than 10 minutes' surgery if the module system is to
remain intact.
******)
    fun headRef (Bind (_,_,_,t)) = headRef t
      | headRef (Ref br) = br
      | headRef (App ((f,_),_)) = headRef f
      | headRef _ = raise Match
    fun is_constructor br =
       (let val nam = ref_nam br
            val fam = headRef (ref_typ br)
            val deps = ref_deps fam
        in  case ref_kind br
              of Constructor _ => true
               | Bnd => ((ref_bind br)=Lda) andalso
                        (member nam deps)
               | _ => false
        end
        handle _ => false)

fun remdup [] = []
  | remdup (x::xs) = let val xs' = remdup xs
                     in  if member x xs' then xs' else x::xs'
                     end

fun shareHoles vhs nom T =
    let val hs = remdup (listHole T [])
        val (VC,(zap,paz)) = copyCtxt holeldav vhs
        fun tables [] = ([],[],paz)
          | tables (h::hs) =
            let val hT = snd (Synt.goaln h)
                val hn = string_of_num h
                val hb = noo ((Lda,Vis),"Goal"^hn) ("Goal",h) ([],hT)
                val (HC,hsbst,hal) = tables hs
            in  (hb::HC,(h,Ref hb)::hsbst,(hb,Var ((h,Bot),hT))::hal)
            end
        val (HC,hsbst,hal) = tables hs
        val LC = HC@VC
        fun mangle _ t = Mod (hsbst $>> t)
        val (LC,LT) = zap %>>> (mangle >>> (LC,T))
        val LC = vootopsort LC
        val Hdef = noo ((Let,Def),nom) ("share",1) (LC,LT)
        val (daa,dvv) = ArgsAndVis (fn x => hal %>> x) LC
    in (Hdef,MkApp ((Ref Hdef,daa),dvv))
    end

        
