(*****************************************************************)
(******                                                     ******)
(******      Useful natural number stuff                    ******)
(******                                                     ******)
(*****************************************************************)

fun Thud () = raise RequireFailure

fun vooNumberDemon [N] =
   (let val n = atoi N
        val _ = if n<0 then Thud () else ()
        val nat  = Req ["nat"]
        val zero = Req ["nat","zero"]
        val suc  = Req ["nat","suc"]
        fun doit 0 = zero
          | doit x = App ((suc,[doit (x-1)]),[ShowNorm])
    in  (doit n,nat)
    end
    handle _ => Thud ())
  | vooNumberDemon _ = Thud ()

val _ = addVooDemon vooNumberDemon

fun vooNatNoCyclesDemon ["nat","no","cycles"] =
   (let val NNC = on (start (?"{n|%nat%}(%Eq% n (%nat suc% n))->{A|Type}A"))
                  [introvool ["n","e"] 1 1,
                   vooGoal [("type",1),("nnc",1)] ("goal",1),
                   Elim MaximalStrat (?"%nat elim%") [("goal",1),("n",1)],
                   conflictTac ("subgoal",1) ("e",1),
                   injectTac ("subgoal",2) ("e",1),
                   vooattack ("subgoal",2) ("zob",1),
                   vooIntroNTac 2 ("zob",1),
                   vooAssumption,
                   vookcatta ("subgoal",2)]
    in  vooQED [("type",1),("nnc",1)] ["nat","no","cycles"] NNC
    end
    handle _ => Thud ())
  | vooNatNoCyclesDemon _ = Thud ()

val _ = addVooDemon vooNatNoCyclesDemon
