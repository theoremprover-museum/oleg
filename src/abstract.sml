(***************************************************************)
(* the magic abstractor                                        *)
(***************************************************************)

fun vvt v = (v,whnf (type_of_constr v))

fun Grab (C,t) (id as (nom,num)) s =
    let val Q = Req ["Eq"]
        val ds1 = Req ["dep","subst","1"]
        val S = type_of_constr s
        val x = noo ((Pi,Hid),nom) id ([],S)
        val qnom = nom^"_q"
        val qid = (qnom,num)
        val q = noo ((Pi,Vis),qnom) qid
                    ([],App ((Q,[S,Ref x,s]),[NoShow,ShowNorm,ShowNorm]))
        val dsq = synthApp ds1 (Ref q) ShowNorm
        fun capture u = case $!([x],u)
                          of (Bind ((Pi,Hid),n,dom,ran)) =>
                              vooeta (Bind ((Lda,Vis),n,dom,ran))
                           | _ => failwith "shouldn't happen"
        fun adapt (u,U) = if depends x U
                          then MkApp ((dsq,[capture U,u]),[ShowNorm,ShowNorm])
                          else u
        fun glapp fF [] [] = fF
          | glapp (f,F) ((a,A)::aaAA) (v::vv) =
           (case F
              of Bind ((Pi,_),_,dom,_) =>
                (case par_unif [] dom A
                   of SOME [] => glapp (vvt (MkApp ((f,[a]),[v]))) aaAA vv
                    | _ => 
                      glapp (vvt (MkApp ((adapt (f,F),[adapt (a,A)]),[v])))
                            aaAA vv)
               | _ => failwith "funny function")
          | glapp _ _ _ = failwith "function zip problem"
        fun rab (uU as (u,U)) = case par_unif [] s u
                                  of SOME [] => (Ref x,U)
                                   | _ => ab uU
        and ab (uU as (Ref _,_)) = uU
          | ab (App ((f,aa),vv),_) =
            let val fF' = rab (vvt f)
                val aaAA' = map (rab o vvt) aa
            in  glapp fF' aaAA' vv
            end
          | ab _ = failwith "too stupid right now"
    in  (q::x::C,adapt (rab (vvt t)))
    end

fun updateVoo b V =
    let val (v,t) = vvt ($!V)
        val (bv,nom,_,_) = ref_bd b
    in  (b<:(bv,nom,v,t))<!(Voo (bid b,V))
    end

fun vooGrab q =
    let val Q = Req ["Eq"]
        val ds1 = Req ["dep","subst","1"]
        val (x,rx,s,S) =
            case (type_of_constr q)
              of App ((Q',[S,rx as Ref x,s]),_) =>
                 if sameTerm Q Q' then (x,rx,s,S)
                 else failwith "can't do owt wi'that!"
               | _ => failwith "can't do owt wi'that!"
        val dsq = synthApp ds1 q ShowNorm
        fun capture u = case $!([x],u)
                          of (Bind ((Pi,Hid),n,dom,ran)) =>
                              vooeta (Bind ((Lda,Vis),n,dom,ran))
                           | _ => failwith "shouldn't happen"
        fun adapt (u,U) = if depends x U
                          then MkApp ((dsq,[capture U,u]),[ShowNorm,ShowNorm])
                          else u
        fun glapp fF [] [] = fF
          | glapp (f,F) ((a,A)::aaAA) (v::vv) =
           (case F
              of Bind ((Pi,_),_,dom,_) =>
                (case par_unif [] dom A
                   of SOME [] => glapp (vvt (MkApp ((f,[a]),[v]))) aaAA vv
                    | _ => 
                      glapp (vvt (MkApp ((adapt (f,F),[adapt (a,A)]),[v])))
                            aaAA vv)
               | _ => failwith "funny function")
          | glapp _ _ _ = failwith "function zip problem"
        fun rab (uU as (u,U)) = case par_unif [] s u
                                  of SOME [] => (Ref x,U)
                                   | _ => ab uU
        and ab (uU as (Ref _,_)) = uU
          | ab (App ((f,aa),vv),_) =
            let val fF' = rab (vvt f)
                val aaAA' = map (rab o vvt) aa
            in  glapp fF' aaAA' vv
            end
          | ab (b as Bind _,_) =
               vvt ($!(ctab (introall iota "ab" 1 ([],b))))
          | ab _ = failwith "too stupid right now"
        and ctab (C,t) =
            (vooctxtrec
             {hitBot=fn _ => [],hitDom=fn _ => failwith "too stupid right now",
              hitVoo=fn (_,D) => fn b => fn _ => fn rect =>
                     let val C' = rect ()
                     in  (updateVoo b (ctab D))::C'
                     end}
             C,#1 (rab (vvt t)))
    in  ctab
    end
