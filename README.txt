This directory contains the current samizdat version of OLEG, specifically

  src            the source code (still needs SML/NJ 0.93)
  bin            linux binaries compiled from the above
  examples       some demo scripts
  papers         related old drafts of papers now changed beyond recognition
                   (and generally for the better)
  emacs-hack.el  not so much an oleg mode; more a nightmare of comint and
                   font-lock


Things you might like to know


(1)  EMACS GADGETS

     Try adjusting the code in emacs-hack.el to point to your oleg binary,
     then run it when you start emacs (e.g. by pasting it into .emacs).
     Now, when you've just loaded an oleg script, do M-x run-lego and it'll
     start an oleg process for you. Moreover, the tab key in the script
     buffer will send a line to the oleg process. More moreover, most things
     will get coloured in properly.
  
     It's not even Proof Lance Corporal, but it's better than a poke in the
     eye.

     By the way, if things start going really slowly, try watching in black
     and white...


(2)  LIBRARY

     Er. Sorry about that. I can't quite remember how, but I seem to have
     broken the module system at some point---it's incompatible in some way
     with the labelling mechanism or something.

     Anyhow, the library as was isn't so useful for oleg development. On
     the other hand, you'll notice that each of the example files has the
     same prelude. More or less. I guess it could be an include file.


(3)  EXAMPLES

     BasicProg.l  demonstrates the basics of the exciting new programming
                    tactics
     TypeCheck.l  is the implementation of the typechecker from VfL version I
                    (the early funny one---see PAPERS)
     TYPES03.l    is the demo script used at TYPES 2003, in which we have
                    the joy of gcd
     Exception.l  is the code and correctness proof for my variation on the
                    theme of Hutton and Wright's compiler-with-exceptions;
                    as advertized in their paper
     Unify.l      if the code and correctness proof for first order unification
                    by structural recursion (see PAPERS)


(4)  PAPERS

     old-elim.ps  is the original no-you-can't-fit-all-that-in-19-pages
                    version of EwaM, which attempts to be forthcoming about
                    no confusion and no cycle proofs, and has some moderately
                    provocative ideas about what the gadgets might be good
                    for; most of which got censored, in favour of doing one
                    job well...
     view-I.ps    is the earlier funnier (and shorter) version of VfL; whilst
                    anonymous referees provoked significant improvements
                    and much useful work on elaboration, I do feel that the
                    official version has lost (a) the emphasis on interactive
                    programming (like we do it in oleg) and (b) the feeling
                    of how much fun it is to work this way, rather than how
                    hard you have to work to make a machine believe in it...
     unify.ps     is actually quite close to the real thing, and
     proof.ps     is the correctness proof which nobody read, but is actually
                    quite cool; the Unify.l file follows this pretty closely


(5)  EQUALITY

     The Elim, KJunify and Program X tactics all use John Major equality,
     but Qrepl (and its monster-in-the-basement chum Wave) still use
     Martin-Lof equality. Also, some of the gadget-makers expect to find
     M-L eq. So we need both. Sometimes we need to convert between the two.
     Not so hard.


(6)  GADGETS

     The brackets (!...!) enclose tags---the codes oleg tactics use to refer
     to constructions they exploit. The Generate tactic attempts to find a
     provider for the construction with a given tag. The Label tactic
     maps a tag to a given construction.

     Gadget generation is no longer automatically triggered when you
     declare an inductive datatype. Trigger it yourself, thus

       Inductive [Nat : Type] Constructors
         [zero : Nat]
         [suc  : {n:Nat}Nat];
       Generate (!Nat cases!);    (* the case analysis principle *)
       Generate (!Nat eduardo!);  (* the recursion principle *)

     Note that generating `eduardo' relies on finding

       Inductive [Unit  : Type] Constructors [void : Unit];
       Label (!unit!) Unit;
       Label (!unit void!) void;

     to provide the trivial memo structure.

     The gadgets which prove no confusion still generate the M-L equality
     version. Ugh! I never got around to automating the much simpler JM
     construction, although you can find the template in the example
     files. Here it is again

       [Absurd = {T:Type}T];

       Goal {x,y:Nat}Type;
       Program NatNoConfStmt x y;        (* compute matrix of statements *)
         Program Elim (!Nat cases!) x;
           Program Elim (!Nat cases!) y;
             Program Refine {Phi:Type}Phi->Phi;
             Program Refine Absurd;
           Program Elim (!Nat cases!) y;
             Program Refine Absurd;
             Program Names y x;
               Program Refine {Phi:Type}((x == y)->Phi)->Phi;
       Program Save;
        
       Goal {x,y:Nat}{q:x == y}{tg:Target q}NatNoConfStmt x y;
       Program NatNoConf x y q tg;       (* justify the injective diagonal *)
         Program Elim (!JM elim!) q;
           Program Elim (!Nat cases!) x;
             Program Refine [Phi:Type][phi:Phi]phi;
             Program Refine [Phi:Type][phi:(n == n)->Phi]phi (JMr n);
       Program Save;  
     
       Label (!Nat noConf!) NatNoConf;   (* tell KJunify *)

     Er, also, the effect of

       Label (!nat zero!) zero;
       Label (!nat suc!) suc;

     is to allow (!3!) to abbreviate suc (suc (suc zero)) and so on. Sadly
     only on the input side.


(7)  ELIMINATION

       Elim rule target ... target;

     eliminates with the given rule, after unifying the provided targets
     with the expressions marked as {tg:Target exp} in the rule's type;
     if the rule is not marked up in that way, Elim kind of guesses what
     to do with the targets you provide (in such a way that regular _elim
     rules are properly handled). Subgoal simplification by unification is
     automatic.


(8)  UNIFICATION

       KJunify;

     should actually be called JMunify

     relies on you providing (!Blah noConf!) for each family Blah you need
     to work with; see above recipe


(7)  NAMING HYPOTHESES

       Names x1 x2 x3 ...;

     (re)names the hyps in the goal without intros-ing them; long overdue


(8)  ABSTRACTION

       Abst x exp;

     abstracts every occurrence of exp from the goal as a new hyp called x;
     can cope with exp living under a prefix of hyps---x goes as far left as
     possible

       AbstEq x q exp;

     similar, but also keeps {q:x == exp} as a hyp; wot a larf!

     Examples can be found in Exception.l and Unify.l


(9)  REWRITING

       Wave > lawsProof;
       Wave < lawsProof;

     Wave is a multiple rewriting tactic. lawsProof is a term of type

       ({x:X}... (Eq l[x...] r[x...])) # ... # ({x:X}... (Eq l[x...] r[x...]))

     ie a tuple of universally quantified equations. Wave tries to
     rewrite like billyo, following these laws, in the direction you
     indicate. It's stupid, unsubtle (and potentially unsafe if you
     choose dangerous laws). But it doesn't lie to the typechecker.
     More safety is achievable via the gasoline-controlled version

       Wave n > lawsProof;
       Wave n < lawsProof;

     which limits the number of iterations allowed.

     Favourite applications include

       Wave > (plusAbsorbsZero,plusAssociative);

     Note the use of M-L Eq rather than JM ==. Also, Wave is not smart
     enough to rewrite under hypotheses.

     Examples in Unify.l


(10) PROGRAMMING

     Thrilling new programming tools!

     If your goal is

       ?0 : {x1:S1}...{xn:Sn}T

     and you say

       Program f x1 ... xn;

     you turn your goal into a programming problem! The new Program Blah
     tactics help you solve it! Read on...


(11) PROGRAMMING INFORMATION

     After the execution of each Program Blah tactic, you get not only the
     proof state, but the program state comprising

       (*) the type signatures of the programs currently under development
       (*) their code so far
       (*) information local to the bit of code you're supposed to write next

     All of this information is actually represented in the proof state,
     which comprises goals of form

       (*) {...}T_myFun p1 ... pn
             the unsolved programming problems
       (*) <myFun:{...}T>(myFun == [...]vomit[T_myFun goals])
             the ghastly proof term, so far
       (*) {...}U_myFun p1 ... pn
             one for each lhs, solved or not

     The program signatures are computed from the <myFun> goals; the
     program code is computed by running the ghastly term so far for each
     lhs given by the U_myFun goals.

     By the way, T_myFun is just a frozen function which computes the
     return type of your program. call_myFun and ret_myFun map between
     the two in the obvious (but frozen way). U_myFun is just a frozen
     function which computes a trivial Prop. Don't worry, they'll thaw
     out later.

       Program; (* with no args, note *)

     attempts to generate and print the program state, if you've
     lost it for some reason, eg hand-cranking a bit of the construction.


(12) PROGRAMMING TACTICS

       Program Elim rule target;

     splits a programming problem by rule on target;
     ie does elimination on the given target with the given rule to both the
     T_ goal and the U_ goal

       Program Refine blah;

     fills in blah as the right-hand side of the current goal;
     ie solves the relevant T_ goal (having first tried to extract recursive
     calls from T_ hypotheses); warning---sometimes the latter mechanism
     commits to a T_ hyp too early, leaving unsolvable equations as subgoals
     (hence the hand-cranking in gcd in TYPES03.l)

       Program Names x1 ... xn;

     renames pattern variables (often needed in induction-then-cases progs);
     warning---sometimes muddles the goals up, leaving no programming problem
     topmost, but nothing that Next can't cure.

       Program Abst myFriend arg ... arg;

     generates a programming problem for a helper function taking the given
     args, which are usually existing pattern vars or some (var as exp),
     where exp is an intermediate value you'd like abstracted, and var is
     what it gets called; by a miracle of modern technology, the helper
     function can still remember how to do recursive calls to the master
     function.


(13) KEEPING A PROGRAM

       Program Save;

     should be called when you've filled in all the bits of program and
     killed off any proof obligations apart from the <myFun> and U_ goals.
     It unfreezes what it needs to solve these goals, then after QED, it
     saves the big nasty term as the defined value of the function, freezes
     it, and gives it (iota) reduction rules instead. Freeze/Unfreeze toggles
     whether it's iota/delta reduction for that symbol.


(14) MYSTERIOUS Forget/KillRef PROBLEM

     I've got some sort of bureaucratic cockup in the lego-state/proof-state/
     twilight-zone, which means that retrograde steps sometimes throw away
     too much (e.g. KillRef discarding the reduction rules you just saved,
     or some such). I recommend ripping it all up and starting again.
     Computers are fast. OK, it's still a pain. Undo in proof state is still
     ok. Phew.


(15) SUPPORT

     Choke. Cough. Splutter.


(16) HAVE FUN

     No really, this is possible.
