fun targName s = String.>=(s,"Target") andalso String.<(s,"Targeu")

exception targFail

fun Target rule =
    let fun targ_hnf t =
            case dnf t (* dodgy or what *)
              of t as (Bind ((Let,Def),s,d,b)) =>
                 if targName s then t else targ_hnf (subst1 d b)
               | t => whnf t

        fun targo (Bind ((Let,Def),s,_,_)) = not (targName s)
          | targo _ = true

        fun nextc [] = 1
          | nextc (b::_) = 1+(#2 (bid b))

        fun Targ embryo R c [] S = (S,embryo)
          | Targ embryo R c (h::t) (S as (SC,ST)) =
           (case (introtestmangall targo iota targ_hnf "arg" c R)
              of (RC,Bind ((Let,Def),_,d,b)) => (* it's a targetter *)
                 let val SC' = RC@SC
                     val (aa,vv) = ArgsAndVis iota RC
                     val RC = map pihole RC
                     val embryo' = MkApp ((embryo,aa),vv)
                     val c' = nextc SC'
                     val R' = ([],b)
                     val H = type_of_constr h
                     val D = type_of_constr d
                 in  case par_unif [] H D
                       of NONE   => raise targFail
                        | SOME s => 
                    (case par_unif s h d
                       of NONE   => raise targFail
                        | SOME s => Targ (s $>> embryo')
                                         (s $>>> R') c' t
                                         (s $>>> (SC',ST)))
                 end
               | _ => raise targFail)
    in Targ rule ([],type_of_constr rule) 1
    end

