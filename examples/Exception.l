(***** Prelude **************************************************************)

[SET=Type(0)]
[TYPE=Type];
[TYPE_minus1 : TYPE =Type]
[TYPE_minus2 : TYPE_minus1 =Type];


$[Target : {A|Type}A->Type]
$[on : {A|Type}{a:A}Target a];
Label (!Target!) Target;
Label (!Target on!) on;


(***** JM Equality **********************************************************)

$[op== : {A,B|Type}A->B->Prop // JMr];
Configure Infix == right 2;

$[JMr : {A|Type}{x:A}x == x];

$[JM_elim : {A|Type}{a:A}{P:{b:A}(a == b)->Type}(P a (JMr a))->
		{b:A}{q:a == b}{tg:Target q}P b q];

[[A:Type][a,b:A][P:{b:A}(a == b)->Type][p:P a (JMr a)][tg:Target (JMr a)]
  JM_elim a P p a (JMr a) tg ==> p
];

Label (!JM!) op==;
Label (!JM refl!) JMr;
Label (!JM elim!) JM_elim;

Goal JM_J : {A|Type}{a,b|A}{q:a == b}{tg:Target q}
            {Phi:A->Type}{phi:Phi a}Phi b;
Elim (!JM elim!) q;
  intros; Immed;
Save;
Label (!JM J!) JM_J;

Goal JM_Jsym : {A|Type}{b,a|A}{q:b == a}{tg:Target q}
               {Phi:A->Type}{phi:Phi a}Phi b;
Elim (!JM elim!) q;
  intros; Immed;
Save;
Label (!JM Jsym!) JM_Jsym;

Goal JM_K : {A|Type}{a|A}{q:a == a}{tg:Target q}
            {Phi:(a == a)->Type}{phi:Phi (JMr a)}Phi q;
Elim (!JM elim!) q;
  intros; Immed;
Save;
Label (!JM K!) JM_K;

Goal JMresp : {S,T|Type}{f:S->T}{x,y|S}{q:x == y}((f x) == (f y));
KJunify;
  intros; Refine JMr;
Save;

Goal JMapp : {S,T|Type}{f,g:S->T}{x,y|S}{q1:f == g}{q2:x == y}((f x) == (g y));
KJunify;
  intros; Refine JMr;
Save;

Goal JMsym : {T|Type}{x,y|T}{q:x == y}(y == x);
KJunify;
  intros; Refine JMr;
Save;

Goal JMtrans : {T|Type}{x,y,z|T}{q:x == y}(y == z)->(x == z);
KJunify;
  intros; Refine JMr;
Save;



(***** M-L Equality (needed for Theorems) ***********************************)

$[Eq : {t|Type}t->t->Prop // Eqr];

$[Eqr : {t|Type}{x:t}Eq x x];

$[Eq_elim : {t|Type}{P:{x,y:t}(Eq x y)->Type}({x:t}P x x (Eqr x))->
		{x,y:t}{p:Eq x y}P x y p];

[[t:Type]
 [P:{x,y:t}(Eq x y)->Type]
 [h:{x:t}P x x (Eqr x)]
 [x:t]
    Eq_elim P h x x (Eqr x) ==> h x];


Goal Eq_refl : {T|Type}{t:T}Eq t t;
	intros;
	Refine Eqr;
SaveUnfrozen Eq_refl;		(* otherwise Eq_unique can't be proven *)

Goal Eq_subst : {t|Type}{m,n|t}(Eq m n)->{P:t->Type}(P m)->P n;
        Intros ___;
        Refine Eq_elim|t ([x,y:t][_:Eq x y]{P:t->Type}(P x)->P y);
        Intros ___;
        Immed;
Save Eq_subst;

Label (!Eq!) Eq;
Label (!Eq refl!) Eq_refl;
Label (!Eq elim!) Eq_elim;
Label (!Eq subst!) Eq_subst;

Generate (!Eq J sym!);

Generate (!Eq sym!);

[trueProp = {P:Prop}P->P];
[trueProof = [P:Prop][p:P]p : trueProp];

Label (!any inhabited type!) trueProp;
Label (!any inhabited type term!) trueProof;

Goal Rew : {A|Type}{x,y|A}{q:x == y}Eq x y;
KJunify;
  intros; Refine Eq_refl;
Save;


(****** the unit type *******************************************************)

Inductive [Wait : Type] Constructors [go : Wait];
Label (!unit!) Wait;
Label (!unit void!) go;
Generate (!Wait cases!);

(***** logical bits and pieces **********************************************)

[P,Q?Prop];
[and = {R|Prop}(P->Q->R)->R];
Discharge P;
Configure Infix /\ right 2;

[FF = {P|Prop}P];

[EQ [S,T|SET][f,g:S -> T] = {x:S}(f x) == (g x)];

Goal {S,T|SET}{f|S -> T}EQ f f;
Intros; Refine JMr;
Save EQrefl;

Goal {S,T|SET}{f,g|S -> T}(EQ f g)->EQ g f;
Intros;
  Refine JMsym;
    Immed;
Save EQsym;

Goal {S,T|SET}{f,g,h|S -> T}(EQ f g)->(EQ g h)->EQ f h;
Intros;
  Refine JMtrans;
    Immed;
Save EQtrans;

[EX [X|SET][P:X->Prop] = {Q:Prop}({x:X}(P x)->Q)->Q];


(***** functional bits and pieces *******************************************)

Configure Infix &o right 3;
Goal {R,S,T|SET}(S -> T)->(R -> S)->R -> T;
Program op&o R S T f g x;
  Program Refine f (g x);
Program Save;


(****** Nat *****************************************************************)

Inductive [Nat:SET] Constructors
  [zero:Nat]
  [suc:{n:Nat}Nat];
Generate (!Nat eduardo!);

[Absurd = {T:Type}T];

Goal {x,y:Nat}Type;
Program NatNoConfStmt x y;
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
Program NatNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!Nat cases!) x;
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:(n == n)->Phi]phi (JMr n);
Program Save;  

Label (!Nat noConf!) NatNoConf;


Configure Infix + right 4;
Goal Nat -> Nat -> Nat;
Program op+ x y;
  Program Elim (!Nat elim!) x;
    Program Refine y;
    Program Refine suc (n + y);
Program Save;


(***** Maybe ****************************************************************)

[T?SET];
Inductive [Maybe:SET] Constructors
  [no:Maybe]
  [yes:{t:T}Maybe];
Generate (!Maybe cases!);

Goal {x,y:Maybe}Type;
Program MaybeNoConfStmt x y;
  Program Elim (!Maybe cases!) x;
    Program Elim (!Maybe cases!) y;
      Program Refine {Phi:Type}Phi->Phi;
      Program Refine Absurd;
    Program Elim (!Maybe cases!) y;
      Program Refine Absurd;
      Program Names y x;
        Program Refine {Phi:Type}((x == y)->Phi)->Phi;
Program Save;
 
Goal {x,y:Maybe}{q:x == y}{tg:Target q}MaybeNoConfStmt x y;
Program MaybeNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!Maybe cases!) x;
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:(t == t)->Phi]phi (JMr t);
Program Save;  

Label (!Maybe noConf!) MaybeNoConf;

Discharge T;

Goal {S,T|SET}(S -> T) -> S -> Maybe T;
Program may S T f s;
  Program Refine yes (f s);
Program Save;

Configure Infix &yam left 4;
Goal {S,T|SET}(S -> Maybe T) -> (Maybe S) -> Maybe T;
Program op&yam S T f ms;
  Program Elim (!Maybe cases!) ms;
    Program Refine no;
    Program Refine f t;
Program Save;

Configure Infix &mapp left 3;
Goal {S,T|SET}(Maybe (S -> T)) -> (Maybe S) -> Maybe T;
Program op&mapp S T mf ms;
  Program Elim (!Maybe cases!) mf;
    Program Refine no;
    Program Names S T f;
      Program Elim (!Maybe cases!) ms;
        Program Refine no;
        Program Refine may f t;
Program Save;


(**************************************************************************)

Inductive [SigEntry : SET] Constructors
  [NAT,HANDLE : SigEntry];
Generate (!SigEntry cases!);

Goal {x,y:SigEntry}Type;
Program SigEntryNoConfStmt x y;
  Program Elim (!SigEntry cases!) x;
    Program Elim (!SigEntry cases!) y;
      Program Refine {Phi:Type}Phi->Phi;
      Program Refine Absurd;
    Program Elim (!SigEntry cases!) y;
      Program Refine Absurd;
      Program Refine {Phi:Type}Phi->Phi;
Program Save;
 
Goal {x,y:SigEntry}{q:x == y}{tg:Target q}SigEntryNoConfStmt x y;
Program SigEntryNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!SigEntry cases!) x;
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:Phi]phi;
Program Save;  

Label (!SigEntry noConf!) SigEntryNoConf;

Inductive [Sig : SET] Constructors
  [NIL : Sig]
  [op&S : {S:Sig}{E:SigEntry}Sig];
Configure Infix &S left 8;
Generate (!Sig eduardo!);

Goal {x,y:Sig}Type;
Program SigNoConfStmt x y;
  Program Elim (!Sig cases!) x;
    Program Elim (!Sig cases!) y;
      Program Refine {Phi:Type}Phi->Phi;
      Program Refine Absurd;
    Program Elim (!Sig cases!) y;
      Program Refine Absurd;
      Program Names S2 E2 S1 E1;
        Program Refine {Phi:Type}((S1 == S2)->(E1 == E2)->Phi)->Phi;
Program Save;
 
Goal {x,y:Sig}{q:x == y}{tg:Target q}SigNoConfStmt x y;
Program SigNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!Sig cases!) x;
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:(S == S)->(E == E)->Phi]
                       phi (JMr S) (JMr E);
Program Save;  

Label (!Sig noConf!) SigNoConf;

Inductive [Stk : Sig -> SET] Constructors
  [nil : Stk NIL]
  [op&n : {S|Sig}{s:Stk S}{n:Nat}Stk (S &S NAT)]
  [op&h : {S|Sig}{s:Stk S}{han:Wait -> Maybe Nat}Stk (S &S HANDLE)];
Configure Infix &n left 4;
Configure Infix &h left 4;
Generate (!Stk eduardo!);


Configure Infix >> right 7;
Inductive [op>> : Sig -> Sig -> SET] Constructors
  [SKIP : {S|Sig}S >> S]
  [op@S : {R,S,T|Sig}{e1:R >> S}{e2:S >> T}R >> T]
  [ADD : {S|Sig}S &S NAT &S NAT >> S &S NAT]
  [PUSH : {n:Nat}{S|Sig}S >> S &S NAT]
  [THROW : {S|Sig}S >> (S &S NAT)]
  [op@CATCH : {S|Sig}{e:S &S HANDLE >> S &S HANDLE &S NAT}
                  {h:S >> S &S NAT}
                  S >> S &S NAT];
Configure Infix @S right 3;
Configure Infix @CATCH right 4;
Generate (!op>> eduardo!);

Goal {S|Sig}(Stk (S &S HANDLE &S NAT))->Stk (S &S NAT);
Program relax S s;
  Program Elim (!Stk cases!) s;
    Program Elim (!Stk cases!) s;
      Program Refine s &n n;
Program Save;

[Gimme [S:Sig] = (Stk S) -> Wait -> Maybe Nat];

Goal {S|Sig}(Stk S)->Maybe Nat;
Program unwind S s;
  Program Elim (!Stk elim!) s;
    Program Refine no;
    Program Refine unwind s;
    Program Refine han go;
Program Save;


Goal {S,T|Sig}{p:S >> T}{goon : Gimme T}Gimme S;
Program exec S T p goon s wait;
  Program Elim (!op>> eduardo!) p;
    Program Elim (!Wait cases!) wait;
    Program Names S T p goon s;
          Program Elim (!op>> cases!) p;
            Program Refine goon s go;
              Intros R S T e1 e2 memo goon s;
                Refine ret_exec;
                  Refine call_exec|?|?|e1|?|s|go|memo.1.2;
                    Intros s' wait;
                      Refine call_exec|?|?|e2|goon|s'|wait|memo.2.2;
              Program;
              Program Elim (!Stk cases!) s;
                Program Elim (!Stk cases!) s;
                  Program Names S s m n;
                    Program Refine goon (s &n (m + n)) go;
              Next 17; Program;
                Program Refine goon (s &n n) go;
              Next 18; Program;
                Program Refine unwind s;
              Next 19; Program;
                Intros S e h memo goon s;
                  Refine ret_exec;
                    Refine call_exec|?|?|e|(goon &o relax)|?|go|memo.1.2;
                      Refine (s &h ?);
                        Intros wait;
                          Refine call_exec|?|?|h|goon|s|wait|memo.2.2;
              Program;
Program Save;

Goal Gimme (NIL &S NAT);
Program stop s wait;
  Program Elim (!Wait cases!) wait;
    Program Elim (!Stk elim!) s;
      Program Elim (!Stk elim!) s;
        Program Refine yes n;
Program Save;

Label (!nat!) Nat;
Label (!nat zero!) zero;
Label (!nat suc!) suc;

[run [p:NIL >> NIL &S NAT] = exec p stop nil go];

Inductive [Exp : SET] Constructors
  [val : Nat -> Exp]
  [plus : {x,y:Exp}Exp]
  [throw : Exp]
  [catch : {e,h:Exp}Exp];
Generate (!Exp eduardo!);

Goal Exp -> Maybe Nat;
Program eval e;
  Program Elim (!Exp elim!) e;
    Program Refine yes x1;
    Program Refine yes op+ &mapp eval x &mapp eval y;
    Program Refine no;
    Program Abst evalcatch (v as eval e) h;
      Program Elim (!Maybe cases!) v;
        Program Refine eval h;
        Program Refine yes t;
Program Save;

Goal {S|Sig}Exp -> (S >> S &S NAT);
Program compile S e;
  Program Elim (!Exp elim!) e;
    Program Refine PUSH x1;
    Program Refine compile|S x @S compile|(S &S NAT) y @S ADD;
    Program Refine THROW;
    Program Refine (compile|(S &S HANDLE) e) @CATCH (compile|S h);
Program Save;

Inductive [OK : {e:Exp}{mn:Maybe Nat}
                {S|Sig}{s:Stk S}{goon:Gimme (S &S NAT)}{t:Maybe Nat}
                SET]
Constructors
  [succeeds : {e:Exp}{n:Nat}
              {S|Sig}{s:Stk S}{goon:Gimme (S &S NAT)}
              OK e (yes n) s goon (goon (s &n n) go)]
  [fails    : {e:Exp}
              {S|Sig}{s:Stk S}{goon:Gimme (S &S NAT)}
              OK e (no Nat) s goon (unwind s)];

Goal {e|Exp}{mn|Maybe Nat}{eq:mn == eval e}
     {S|Sig}{s|Stk S}{goon|Gimme (S &S NAT)}{t|Maybe Nat}
     {cq:t == exec (compile|S e) goon s go}
     OK e mn s goon t;
[HintS=succeeds][HintF=fails];
Elim (!Exp elim!) e;
  Intros; Immed;
  Names x y S s goon xH yH;
    AbstEq xv xvq (eval x);
      AbstEq xc xcq
          (exec (compile x)
            ([s':Stk (S &S NAT)][wait:Wait]
             exec (compile y @S ADD|S) goon s' wait) s go);
        Abst Hx (xH (JMr xv) xcq);
          Elim (!OK elim!) Hx;
            AbstEq yv yvq (eval y);
              AbstEq yc ycq
          (exec (compile y)
            ([s':Stk (S &S NAT &S NAT)][wait:Wait]exec (ADD|S) goon s' wait)
            (s &n n) go);
                Abst Hy (yH (JMr yv) ycq);
                  Elim (!OK elim!) Hy Then Intros Then Immed;
            Intros; Immed;
  Intros; Immed;
  Names e h S s goon eH hH;
    AbstEq ev evq (eval e);
      AbstEq ec ecq
          (exec (compile e) (goon &o relax|S)
            (s &h [wait:Wait]exec (compile h) goon s wait) go);
        Abst He (eH (JMr ev) ecq);
          Elim (!OK elim!) He;
            Intros; Immed;
            AbstEq hv hvq (eval h);
              AbstEq hc hcq (exec (compile h) goon s go);
                Abst Hh (hH (JMr hv) hcq);
                  Elim (!OK elim!) Hh Then Intros Then Immed;
Save evalExecCompileOK;
Freeze evalExecCompileOK;

Goal {e:Exp}(eval e == run (compile e));
  AbstEq ev evq eval e;
    AbstEq ec ecq (run (compile e));
      Abst H (evalExecCompileOK evq ecq);
        Elim (!OK elim!) H Then Intros Then Refine JMr;
Save compilerCorrect;




















