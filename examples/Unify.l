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

Inductive [One : Type] Constructors [void : One];
Label (!unit!) One;
Label (!unit void!) void;


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


(***** Fin ******************************************************************)

Inductive [Fin : Nat -> SET] Constructors
  [f0 : {n:Nat}Fin (suc n)]
  [fs : {n|Nat}{i:Fin n}Fin (suc n)];
Generate (!Fin eduardo!);

Goal {m|Nat}{x:Fin m}{n|Nat}{y:Fin n}Type;
Program FinNoConfStmt m x n y;
  Program Elim (!Fin cases!) x;
    Program Elim (!Fin cases!) y;
      Program Names n m;
        Program Refine {Phi:Type}((m == n)->Phi)->Phi;
        Next +1; Program Refine Absurd;
    Next +1; Program Elim (!Fin cases!) y;
      Program Refine Absurd;
      Program Names n y m x;
        Program Refine {Phi:Type}((m == n)->(x == y)->Phi)->Phi;
Program Save;

Goal {n|Nat}{x,y:Fin n}{q:x == y}{tg:Target q}FinNoConfStmt x y;
Program FinNoConf n x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!Fin cases!) x;
      Program Refine [Phi:Type][phi:(n == n)->Phi]phi (JMr n);
      Program Refine [Phi:Type][phi:(n == n)->(i == i)->Phi]
                     phi (JMr n) (JMr i);
Program Save;  

Label (!Fin noConf!) FinNoConf;


(***** thin and thick *******************************************************)

Goal {n|Nat}{x:Fin (suc n)}{y:Fin n}Fin (suc n);
Program thin n x y;
  Program Elim (!Nat eduardo!) n;
    Program Elim (!Fin cases!) x;
      Program Refine fs y;
      Program Elim (!Fin cases!) y;
        Program Refine f0;
        Program Names n y x;
          Program Refine fs (thin x y);
Program Save;

[n|Nat][x:Fin (suc n)];
Inductive [Thick : {y:Fin (suc n)}{mz:Maybe (Fin n)}SET]
Constructors
  [thickQ : Thick x no]
  [thickN : {y:Fin n}Thick (thin x y) (yes y)];
Discharge n;

Goal {n|Nat}{x:Fin (suc n)}{y:Fin (suc n)}Maybe (Fin n);
Program thick n x y;
  Program Elim (!Nat eduardo!) n;
    Program Elim (!Fin cases!) x;
      Program Elim (!Fin cases!) y;
        Program Refine no;
        Program Refine yes i;
      Program Elim (!Nat cases!) n;
        Program Elim (!Fin cases!) i;
        Program Elim (!Fin cases!) y;
          Program Refine yes (f0 n);
          Program Names n y x;
            Program Refine may (fs|n) &yam thick x y;
Program Save;

Goal {n|Nat}{x,y|Fin (suc n)}{mz|Maybe (Fin n)}
     {q:mz == thick x y}Thick x y mz;
Elim (!Nat eduardo!) n;
  Elim (!Fin cases!) x;
    Elim (!Fin cases!) y;
      intros; Refine thickQ;
      intros; Refine thickN;
    Elim (!Nat cases!) n;
      Elim (!Fin cases!) i;
      Elim (!Fin cases!) y;
        intros; Refine thickN ? (f0 n);
        Names n y x h; AbstEq mz q (thick x y);
          Abst ih (h.2 q);
            Elim (!Thick elim!) ih;
              intros; Refine thickQ;     
              intros; Refine thickN ? (fs y);
Save thickThick;
Freeze thickThick;

Goal thinInj : {n|Nat}{x|Fin (suc n)}{y,z|Fin n}
               ((thin x y) == (thin x z)) -> (y == z);
Elim (!Nat eduardo!) n;          
  Elim (!Fin cases!) x;
    intros; Refine JMr;
    Elim (!Fin cases!) y;
      Names n x h z q;
        Elim (!Fin cases!) z;
          intros; Refine JMr;
      Names n y x h z;
        Elim (!Fin cases!) z;
          intros n z y x q h;
            Refine JMresp;
              Refine h.2; Immed;
Save;

Goal thinDiff : {n|Nat}{x|Fin (suc n)}{y|Fin n}{q:(thin x y) == x}Absurd;
Elim (!Nat eduardo!) n;
  Elim (!Fin cases!) x;
    Elim (!Fin cases!) y;
      intros n y x q h;
        Refine h.2; Immed;
Save;

Goal {n|Nat}{x:Fin (suc n)}(thick x x == no (Fin n));
AbstEq mz q (thick x x); Abst h (thickThick q); Elim (!Thick elim!) h;
  intros; Refine JMr;
  intros n x y h q bad dull;
    Refine thinDiff; Immed;
Save thickSame;

Goal {n|Nat}{x:Fin (suc n)}{y:Fin n}(thick x (thin x y) == yes y);
AbstEq mz q (thick x (thin x y)); Abst h (thickThick q); Elim (!Thick elim!) h;
  intros;
    Refine thinDiff (JMsym ?); Immed;
  intros;
    Refine JMresp ? (thinInj ?); Immed;
Save thickThin;


(***** Term and Pos *********************************************************)

[n?Nat];
Inductive [Term : SET] Constructors
  [iota : {i:Fin n}Term]
  [leaf : Term]
  [op&fork : {s,t:Term}Term];
Generate (!Term eduardo!);
Configure Infix &fork left 6;

Goal Term -> Term -> Type;
Program TermNoConfStmt x y;
  Program Elim (!Term cases!) x;
    Program Elim (!Term cases!) y;
      Program Names j i;
        Program Refine {Phi:Type}((i == j)->Phi)->Phi;
        Next +1; Program Refine Absurd;
        Next +1; Program Refine Absurd;
    Next +1; Program Elim (!Term cases!) y;
      Program Refine Absurd;
      Program Refine {Phi:Type}Phi->Phi;
      Program Refine Absurd;
    Program Names s1 t1;
      Program Elim (!Term cases!) y;
        Program Refine Absurd;
        Program Refine Absurd;
        Program Refine {Phi:Type}((s1 == s)->(t1 == t)->Phi)->Phi;
Program Save;

Goal {x,y:Term}{q:x == y}{tg:Target q}TermNoConfStmt x y;
Program TermNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!Term cases!) x;
      Program Refine [Phi:Type][phi:(i == i)->Phi]phi (JMr i);
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:(s == s)->(t == t)->Phi]
                       phi (JMr s) (JMr t);
Program Save;

Label (!Term noConf!) TermNoConf;

Inductive [Pos : SET] Constructors
  [here : Pos]
  [lft  : {p:Pos}{t:Term}Pos]
  [rgt  : {s:Term}{p:Pos}Pos];
Generate (!Pos eduardo!);

Goal Pos -> Pos -> Type;
Program PosNoConfStmt x y;
  Program Elim (!Pos cases!) x;
    Program Elim (!Pos cases!) y;
      Program Refine {Phi:Type}Phi->Phi;
      Program Refine Absurd;
      Program Refine Absurd;
    Program Elim (!Pos cases!) y;
      Program Refine Absurd;
      Program Names p2 t2 p1 t1;
        Program Refine {Phi:Type}((p1 == p2)->(t1 == t2)->Phi)->Phi;
      Next +1; Program Refine Absurd;
    Next +1; Program Elim (!Pos cases!) y;
      Program Refine Absurd;
      Program Refine Absurd;
      Program Names s2 p2 s1 p1;
        Program Refine {Phi:Type}((s1 == s2)->(p1 == p2)->Phi)->Phi;
Program Save;

Goal {x,y:Pos}{q:x == y}{tg:Target q}PosNoConfStmt x y;
Program PosNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!Pos cases!) x;
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:(p == p)->(t == t)->Phi]
                       phi (JMr p) (JMr t);
      Program Refine [Phi:Type][phi:(s == s)->(p == p)->Phi]
                       phi (JMr s) (JMr p);
Program Save;

Label (!Pos noConf!) PosNoConf;

Goal Pos -> Term -> Term;
Program put p u;
  Program Elim (!Pos elim!) p;
    Program Refine u;
    Program Refine put p u &fork t;
    Program Refine s &fork put p u;
Program Save;

Goal Pos -> Pos -> Pos;
Program plus p q;
  Program Elim (!Pos elim!) p;
    Program Refine q;
    Program Refine lft (plus p q) t;
    Program Refine rgt s (plus p q);
Program Save;

Goal {p,q:Pos}{u:Term}(put (plus p q) u) == (put p (put q u));
Elim (!Pos elim!) p;
  intros; Refine JMr;
  intros;
    Refine JMresp ([x:Term]x &fork t);
      Immed;
  intros;
    Refine JMresp;
      Immed;
Save putAction;

Goal {u:Term}{p:Pos}(u == put p u)->(p == here);
Elim (!Term elim!) u;
  Elim (!Pos cases!) p;
    intros; Refine JMr;
  Elim (!Pos cases!) p;
    intros; Refine JMr;
  Elim (!Pos cases!) p;
    intros; Refine JMr;
    intros t p s bad sh th;
      Claim (plus p (lft here t)) == here;
      Claim {q:Pos}((plus q (lft here t)) == here)->FF;
      Refine ?-0 ? ?-1;
      Next +1;
        Elim (!Pos cases!) q;
      Refine sh;
        Qrepl Rew (putAction p (lft here t) s);
        Immed;
    intros s p t bad sh th;
      Claim (plus p (rgt s here)) == here;
      Claim {q:Pos}((plus q (rgt s here)) == here)->FF;
      Refine ?-0 ? ?-1;
      Next +1;
        Elim (!Pos cases!) q;
      Refine th;
        Qrepl Rew (putAction p (rgt s here) t);
        Immed;
Save termNoCycle;

Discharge n;


(***** renaming and substitution *******************************************)

[op>> [m,n:Nat] = (Fin m)->Term n];
Configure Infix >> right 6;

Goal {m,n|Nat}((Fin m) -> Fin n) -> (m >> n);
Program trm m n f x;
  Program Refine iota (f x);
Program Save;

Configure Infix &mrt left 4;
Goal {m,n|Nat}(m >> n) -> (Term m) -> Term n;
Program op&mrt m n f t;
  Program Elim (!Term elim!) t;
    Program Refine f i;
    Program Refine leaf;
    Program Refine (f &mrt s) &fork (f &mrt t);
Program Save;

(* substitution respects EQ *)
Goal {m,n|Nat}{f,g|m >> n}{Q:EQ f g}EQ (op&mrt f) (op&mrt g);
Normal;
  Elim (!Term elim!) x;
    intros; Immed;
    intros; Refine JMr;
    intros; Refine JMapp; Refine JMresp;
      Refine s_ih;
      Refine +1 t_ih;
        Immed;
Save SubstResp;


(***** composition of substitutions *****)

Configure Infix &c right 3;
Goal {l,m,n|Nat}(m >> n) -> (l >> m) -> (l >> n);
Program op&c l m n f g x;
  Program Refine f &mrt (g x);
Program Save;

Goal {m,n|Nat}{f:m >> n}EQ (f &c iota) f;
Normal;
  intros; Refine JMr;
Save SubstIdRight;

Goal {n|Nat}{t:Term n}(iota &mrt t) == t;
Elim (!Term elim!) t;
  intros; Refine JMr;
  intros; Refine JMr;
  intros; Refine JMapp; Refine JMresp;
    Immed;
Save IdSubst;

Goal {m,n|Nat}{f:m >> n}EQ (iota &c f) f;
Normal;
  intros; Refine IdSubst;
Save SubstIdLeft;

Goal {l,m,n|Nat}{f:m >> n}{g:l >> m}
     {t:Term l}((f &c g) &mrt t) == (f &mrt (g &mrt t));
intros _____;
Elim (!Term elim!) t;
  intros; Refine JMr;
  intros; Refine JMr;
  intros; Refine JMapp; Refine JMresp;
    Immed;
Save CompSubst;

[CompRew [l,m,n|Nat][f:m >> n][g:l >> m][t:Term l] = Rew (CompSubst f g t)];

Goal {l,m,n,o|Nat}{f:n >> o}{g:m >> n}{h:l >> m}
     EQ ((f &c g) &c h) (f &c (g &c h));
Normal;
  intros; Refine CompSubst;
Save SubstCompAssoc;

Goal {l,m,n|Nat}{f1,f2|m >> n}{g1,g2|l >> m}
     (EQ f1 f2)->(EQ g1 g2)->EQ (f1 &c g1) (f2 &c g2);
Intros _______ F G x;
  Normal;
    Qrepl Rew (G x);
      Refine SubstResp; Immed;
Save CompRespEQ;


(***** substitution on positions, with related laws *****)

Goal {m,n|Nat}{f:m >> n}{p:Pos m}Pos n;
Program spos m n f p;
  Program Elim (!Pos elim!) p;
    Program Refine here;
    Program Refine lft (spos f p) (f &mrt t);
    Program Refine rgt (f &mrt s) (spos f p);
Program Save;

Goal {m,n|Nat}{f:m >> n}{u:Term m}{p:Pos m}
     (f &mrt (put p u)) == (put (spos f p) (f &mrt u));
intros ____;
  Elim (!Pos elim!) p;
    intros; Refine JMr;
      intros p t ph;
        Refine JMapp; Refine JMresp;
          Immed;
          Refine JMr;
      intros s p ph;
        Refine JMapp; Refine JMresp;
          Immed;
          Refine JMr;
Save SubstPut;


(***** the occur check *****************************************************)

[n|Nat][x:Fin (suc n)];
Inductive [Check : {t:Term (suc n)}{mu:Maybe (Term n)}SET] Constructors
  [checkOK : {u:Term n}Check (trm (thin x) &mrt u) (yes u)]
  [checkKO : {p:Pos (suc n)}Check (put p (iota x)) no];
Discharge n;

Goal {n|Nat}{x:Fin (suc n)}{t:Term (suc n)}Maybe (Term n);
Program check n x t;
  Program Elim (!Term elim!) t;
    Program Refine may iota &yam thick x i;
    Program Refine yes (leaf n);
    Program Refine may (op&fork|n) &yam check x s &mapp check x t;
Program Save;

Goal {n|Nat}{x|Fin (suc n)}{t|Term (suc n)}{mu|Maybe (Term n)}
     {q:mu == check x t}Check x t mu;
Elim (!Term elim!) t;
  AbstEq mj q (thick x i); Abst h (thickThick q); Elim (!Thick elim!) h;
    intros; Refine checkKO ? here;
    intros; Refine checkOK ? (iota y);
  intros; Refine checkOK ? leaf;
  Names n s t x sh th;
    AbstEq mu qu (check x s); Abst hu (sh qu); Elim (!Check elim!) hu;
      AbstEq mv qv (check x t); Abst hv (th qv); Elim (!Check elim!) hv;
        Names n x t s; intros;
          Refine checkOK ? (s &fork t);
        intros;
          Refine checkKO ? (rgt ? p);
    intros;
      Refine checkKO ? (lft p ?);
Save checkCheck;
Freeze checkCheck;


(***** properties of substitutions *****************************************)

(* a property is a predicate which respects EQ *)
[Property [m:Nat] = <P:{n|Nat}(m >> n)->Prop>
                    {n|Nat}{f,g|m >> n}(EQ f g)->(P f)->P g];

(* the conjunction of properties is a property *)
Goal AND : {m|Nat}{P,Q:Property m}Property m;
Intros m P Q # n f;
  Refine P.1 f /\ Q.1 f;
  Dnf;
    Intros ___ fqg PQf; Refine PQf; Intros Pf Qf X wit; Refine wit;
      Refine P.2; Immed;
      Refine Q.2; Immed;
Save;


(***** equivalence of properties *****)

[IMP [m|Nat][P,Q:Property m] =
    {n|Nat}{f:m >> n}(P.1 f) -> Q.1 f
];

[EQUIV [m|Nat][P,Q:Property m] = (IMP P Q) /\ (IMP Q P)];

Goal EQUIVrefl : {m|Nat}{P|Property m}EQUIV P P;
Intros; Refine H;
    Intros; Immed;
    Intros; Immed;
Save;

Goal EQUIVsym : {m|Nat}{P,Q|Property m}{PEQ:EQUIV P Q}EQUIV Q P;
Intros ____; Refine PEQ; Intros PQ QP X wit; Refine wit;
  Immed;
Save;


(***** the property of extending a solution *****)

Goal {m,n|Nat}{P:Property m}{f:m >> n}Property n;
Intros m n P f # o g ;
  Refine P.1 (g &c f);
  Normal;
    intros o g h q;
      Refine P.2 (CompRespEQ q EQrefl);
Save Extends;

Goal {m,n,o|Nat}{P:Property m}{f:m >> n}{g:n >> o}
      EQUIV (Extends (Extends P f) g) (Extends P (g &c f));
Intros; Refine H;
  Normal;
    intros l h;
      Refine P.2 SubstCompAssoc;
  Normal;
    intros l h;
      Refine P.2 (EQsym SubstCompAssoc);
Save ExtendsComp;

Goal {m|Nat}{P:Property m}EQUIV (Extends P iota) P;
Intros; Refine H;
  Intros n f Pfi;
    Refine P.2; Immed;
      Refine SubstIdRight;
  Intros n f Pf;
    Refine P.2; Immed;
      Refine EQsym SubstIdRight;
Save ExtendsId;

Goal {m,n|Nat}{P,Q|Property m}{PEQ:EQUIV P Q}{f,g|m >> n}{feg:EQ f g}
     EQUIV (Extends P f) (Extends Q g);
[Hint = EQrefl];
Intros _____; Refine PEQ; Intros PQ QP f g feg X wit; Refine wit;
  Normal; Intros o h Phf;
    Refine PQ;
      Refine P.2; Immed;
        Refine CompRespEQ; Immed;
  Normal; Intros o h Qhg;
    Refine QP;
      Refine Q.2; Immed;
        Refine CompRespEQ ? (EQsym ?); Immed;
Save ExtendsResp;


(***** the composition ordering on substitutions ************************)

[LE [l,m,n|Nat][f:l >> m][g:l >> n] = EX [h:n >> m]EQ f (h &c g)];

Goal LEdef : {l,m,n|Nat}{f|m >> n}{g|l >> m}{h|l >> n}
             (EQ h (f &c g))->LE h g;
Intros ______ hqfg;
  Intros; Refine H;
    Immed;
Save;

Goal LErefl : {m,n|Nat}{f:m >> n}LE f f;
Intros;
  Refine H iota;
    Refine EQsym SubstIdLeft;
Save;

Goal LEtrans : {l,m,n,o|Nat}
               {f|l >> m}{g|l >> n}{h|l >> o}
               (LE f g)->(LE g h)->LE f h;
Intros l m n o f g h FG GH Q PQ;
  Refine FG; Refine GH;
    Intros gh ghq fg fgq;
      Refine PQ (fg &c gh);
        Refine EQtrans fgq;
            Refine EQtrans ? (EQsym ?);
              Refine +2 SubstCompAssoc;
              Refine CompRespEQ EQrefl ?; Immed;
Save;

Goal LEtop : {m,n|Nat}{f:m >> n}LE f iota;
Intros m n f Q PQ; Refine PQ f;
    Refine SubstIdRight;
Save;

Goal LEcomp : {l,m,n,o|Nat}
              {f|l >> m}{g|l >> n}{h|o >> l}
              (LE f g)->LE (f &c h) (g &c h);
Intros _______ FG Q wit;
  Refine FG;
    Intros fg fgq;
      Refine wit fg;
        Refine EQtrans ? SubstCompAssoc;
            Refine CompRespEQ ? EQrefl; Immed;
Save;

Goal LErespEQ : {l,m,n|Nat}
                {f,g|l >> m}{h,e|(Fin l)->Term n}
                (EQ f g)->(EQ h e)->(LE f h)->LE g e;
Intros;
  Refine H2;
    intros fh fhq;
      Refine H3 fh;
        Refine EQtrans (EQsym ?); Immed;
          Refine EQtrans; Immed;
            Refine CompRespEQ EQrefl ?; Immed;
Save;


(***** the property of being a maximal solution ***************************)

Goal {m|Nat}{P:Property m}Property m;
Intros m P #;
  intros n f;
    Refine and;
      Refine P.1 f;
      Refine {o|Nat}{g:m >> o}(P.1 g)->LE g f;
  Dnf;
  [Hint = EQrefl];
  intros n f g fgq fhyp;
  Refine fhyp;
    intros Pf Ff;
      Intros X wit; Refine wit;
        Refine P.2; Immed;
        intros o h Ph;
          Refine LErespEQ; Immed;
            Refine -0 Ff h Ph;
Save Max;

Goal {m|Nat}{P,Q|Property m}(EQUIV P Q)->IMP (Max P) (Max Q);
Intros ___ PEQ n f MaxPf;
  Refine PEQ; intros PQ QP;
    Refine MaxPf; intros Pf Ff;
      Intros X wit; Refine wit;
        Refine PQ; Immed;
        intros o g Qg; Refine Ff;
          Refine QP; Immed;
Save MaxResp;


(***** downward closure and the Optimist's lemma ************************)

[DClosed [m|Nat][P:Property m]
  = {n,o|Nat}{f|m >> n}{g|m >> o}(LE f g)->(P.1 g)->(P.1 f)
];

Goal {l,m,n,o|Nat}{P,Q|Property l}{DCP:DClosed P}
     {a|l >> m}{p|m >> n}{q|n >> o}
     {pMax:(Max (Extends P a)).1 p}
     {qMax:(Max (Extends Q (p &c a))).1 q}
     (Max (Extends (AND P Q) a)).1 (q &c p);
[Hint=EQrefl];
Intros;
  Refine pMax; Expand Extends; intros Ppa Fp;
    Refine qMax; Expand Extends; intros Qqpa Fq;
      Refine H; Expand Extends AND;
        Intros X wit; Refine wit;
          Refine DCP; Immed;
            Refine LEcomp (LEdef ?); Immed;
            Refine Q.2; Immed;
              Refine EQsym SubstCompAssoc;
        Expand Extends AND;
          intros k g PQga; Refine PQga; intros Pga Qga;
            Refine Fp g Pga; intros h gqhp;
              Refine Fq h;
                Refine Q.2; Immed;
                  Refine EQtrans ? SubstCompAssoc;
                    Refine CompRespEQ; Immed;
                  intros e hqeq;
                    Refine LEtrans ? (LEcomp (LEdef ?)); Immed;
                      Refine LErespEQ ?? LErefl; Immed;
Save OptimistLemma;


(***** failure of a property ********************************************)

[Nothing [m|Nat][P:Property m] = {n|Nat}{f:m >> n}(P.1 f)->FF];

Goal {m|Nat}{P,Q|Property m}(EQUIV P Q)->(Nothing P)->Nothing Q;
Intros m P Q PQ nP n f Qf;
  Refine nP f;
    Refine PQ;
      intros G H; Refine H; Immed;
Save NothingResp;

Goal {m,n|Nat}{P:Property m}{f:m >> n}
     (Nothing P)->Nothing (Extends P f);
Intros m n P f nP o g Pgf;
  Refine nP;
    Immed;
Save StillNothing;

Goal {m,n|Nat}{P,Q:Property m}{a:m >> n}
     (Nothing (Extends P a)) -> Nothing (Extends (AND P Q) a);
Intros m n P Q a NPa o f EPQaf X;
  Refine EPQaf; intros Pfa Qfa;
      Refine NPa f; Immed;
Save NothingLeft;

Goal {m,n,o|Nat}{P,Q|Property m}{a:m >> n}{p:n >> o}
     ((Max (Extends P a)).1 p) -> (Nothing (Extends Q (p &c a))) ->
     Nothing (Extends (AND P Q) a);
Intros m n o P Q a p MPap NEQpa l g EPQga X;
  Refine EPQga; intros Pga Qga;
    Refine MPap; Intros Ppa Fp;
      Refine Fp ? Pga; intros h hqxp;
        Refine NEQpa h;
          Refine Q.2; Immed;
            Refine EQtrans ? SubstCompAssoc;
              Refine CompRespEQ ? EQrefl;
                Immed;
Save NothingRight;


(***** the unification property *****************************************)

Goal Unifies : {m|Nat}{s,t:Term m}Property m;
Intros m s t # n f;
  Refine (f &mrt s) == (f &mrt t);
  Normal;
    Intros n f g q fu;
      Refine JMtrans (JMsym ?) (JMtrans fu ?);
        Refine SubstResp; Immed;
        Refine SubstResp; Immed;
Save;

Goal {m|Nat}{s,t:Term m}DClosed (Unifies s t);
Intros;
  Expand Unifies;
    Refine H; intros h fq;
      Refine JMtrans (SubstResp ?) (JMtrans ? (SubstResp (EQsym ?))); Immed;
        Wave > CompRew;
          Refine JMresp; Immed;
Save UnifiesDClosed;

Goal {m|Nat}{s,t:Term m}EQUIV (Unifies s t) (Unifies t s);
Intros; Refine H;
  Intros; Expand Unifies;
    Refine JMsym; Immed;
  Intros; Expand Unifies;
    Refine JMsym; Immed;
Save UnifSym;

Goal {m|Nat}{s1,t1,s2,t2:Term m}EQUIV (AND (Unifies s1 s2) (Unifies t1 t2))
                                      (Unifies (s1 &fork t1) (s2 &fork t2));
Intros; Refine H;
  Intros n f G; Refine G; Intros;
    Normal; Refine JMapp; Refine JMresp; Immed;
    Normal; KJunify;
      intros n f S T X G; Refine G; Immed;
Save UnifFork;

Goal {m|Nat}{x:Fin (suc m)}{p:Pos (suc m)}{nh:(p == here (suc m))->FF}
     Nothing (Unifies (iota x) (put p (iota x)));
Expand Nothing Unifies;
  intros m x p nh n f;
    Qrepl Rew (SubstPut f (iota x) p);
      intros q;
        [fph = termNoCycle ?? q];
        Claim {r:Pos (suc m)}(spos f r == here n)->(r == here (suc m));
        Refine nh;
          Refine ?+1; Immed;
        Elim (!Pos cases!) r;
          Refine JMr;
Save NoUnifCycle;

Goal {l,m,n|Nat}{f:m >> n}{g:l >> m}{s,t:Term l}
     EQUIV (Extends (Unifies (g &mrt s) (g &mrt t)) f)
           (Extends (Unifies s t) (f &c g));
Intros; Refine H;
  Intros k h; Normal;
    intros q; Refine JMtrans ? (JMtrans q ?);
      Wave > CompRew; Refine JMr;
      Wave > CompRew; Refine JMr;
  Intros k h; Normal;
    intros q; Refine JMtrans ? (JMtrans q ?);
      Wave > CompRew; Refine JMr;
      Wave > CompRew; Refine JMr;
Save UnifAccumulate;

Goal {m,n|Nat}{t:Term m}{f:m >> n} (Max (Extends (Unifies t t) f)).1 iota;
Intros; Refine H;
  Refine JMr;
  intros; Refine LEtop;
Save UnifTriv;


(***** variable elimination ************************************************)

Configure Infix &for right 5;
Goal {n|Nat}{t:Term n}{x:Fin (suc n)}(suc n >> n);
Program op&for n t x y;
  Program Abst for2 n t x (y' as thick x y);
    Program Elim (!Maybe cases!) y';
      Program Refine t;
      Program Names n i t x;
        Program Refine iota i;
Program Save;

Goal {m|Nat}{x:Fin (suc m)}{t':Term m}
     (Max (Unifies (iota x) (trm (thin x) &mrt t'))).1 (t' &for x);
Intros; Refine H;
  Normal;
    Qrepl Rew (thickSame x);
      Refine JMtrans (JMsym IdSubst) (JMtrans SubstResp CompSubst);
        Normal; intros y;
          Qrepl Rew (thickThin x y);
            Refine JMr;
    Intros n f U X wit; Refine wit (f &c (trm (thin x))); Normal; Names y;
      AbstEq mz qz (thick x y); Abst h (thickThick qz); Elim (!Thick elim!) h;
        intros;
          Refine JMtrans ? (JMsym CompSubst); Immed;
        intros; Refine JMr;
Save UnifVar;


(***** the AList structure **************************************************)

Inductive [AList:{m,n:Nat}SET] Constructors
  [anil : {n:Nat}AList n n]
  [asnoc : {m,n|Nat}{sig:AList m n}{t:Term m}{x:Fin (suc m)}AList (suc m) n];
Generate (!AList eduardo!);


(***** its monoidal structure *****)

Configure Infix &a left 4;

Goal {l,m,n|Nat}{rho:AList m n}{sig:AList l m}AList l n;
Program op&a l m n rho sig;
  Program Elim (!AList elim!) sig;
    Program Refine rho;
    Program Refine asnoc (rho &a sig) t x;
Program Save;

Goal {m,n|Nat}{sig:AList m n}(sig == (anil &a sig));
Elim (!AList elim!) sig;
  intros; Refine JMr;
  intros;
    Refine JMapp ??? JMr; Refine JMapp ??? JMr; Refine JMresp;
      Immed;
Save AListIdLeft;

Goal {l,m,n,o|Nat}{tau:AList n o}{sig:AList m n}{rho:AList l m}
       ((tau &a sig) &a rho) == (tau &a (sig &a rho));
Elim (!AList elim!) rho;
  intros; Refine JMr;
  intros l m rho t x hyp n o tau sig;
    Refine JMapp ??? JMr; Refine JMapp ??? JMr; Refine JMresp;
      Immed;
Save AListAssoc;


(***** its action *****)

Goal {m,n|Nat}{sig:AList m n}(m >> n);
Program sub m n sig;
  Program Elim (!AList elim!) sig;
    Program Refine iota;
    Program Refine sub sig &c (t &for x);
Program Save;

Goal {l,m,n|Nat}{rho:AList m n}{sig:AList l m}
     EQ (sub (rho &a sig)) (sub rho &c sub sig);
[Hint = EQrefl];
Elim (!AList elim!) sig;
  Intros; Refine JMr;
  Intros l m sig t x sigh n rho;
    Refine EQtrans CompRespEQ SubstCompAssoc; Immed;
Save SubstAListComp;


(***** dependent pairs ***************************************************)

[A?SET][B?A->SET];
Inductive [Ex:SET] Constructors
  [pr : {a:A}{b:B a}Ex];
Generate (!Ex cases!);

Goal {x,y:Ex}Type;
Program ExNoConfStmt x y;
  Program Elim (!Ex cases!) x;
    Program Names a1 b1;
      Program Elim (!Ex cases!) y;
       Program Refine {Phi:Type}{phi:(a1 == a)->(b1 == b)->Phi}Phi;
Program Save;

Goal {x,y|Ex}{q:x == y}{tg:Target q}ExNoConfStmt x y;
Program ExNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!Ex cases!) x;
      Program Refine [Phi:Type][phi:(a == a)->(b == b)->Phi]
                     phi (JMr a) (JMr b);
Program Save;

Label (!Ex noConf!) ExNoConf;

Discharge A;

(***** packing up alists *****)
Goal {m|Nat}{acc:Ex (AList m)}{t:Term m}{x:Fin (suc m)}Ex (AList (suc m));
Program easnoc m acc t x;
  Program Elim (!Ex cases!) acc;
    Program Refine pr a (asnoc b t x);
Program Save;


(***** flex-flex unification **********************************************)

Goal {m|Nat}{x,y:Fin m}Ex (AList m);
Program flexFlex m x y;
  Program Elim (!Nat cases!) m;
    Program Elim (!Fin cases!) x;
      Program Abst fF2 n x (y' as (thick x y));
        Program Elim (!Maybe cases!) y';
          Program Refine pr (suc n) (anil (suc n));
          Program Refine pr n (asnoc (anil n) (iota t) x);
Program Save;

Goal {m,n|Nat}{x,y|Fin m}{sig|AList m n}
     (pr n sig == flexFlex x y)->(Max (Unifies (iota x) (iota y))).1 (sub sig);
Elim (!Nat cases!) m;
  Elim (!Fin cases!) x;
  AbstEq mz qz (thick x y); Abst h (thickThick qz); Elim (!Thick elim!) h;
    Intros n x qz X wit; Refine wit;
      Refine JMr;
      intros; Refine LEtop;
    Intros n x y qz;
      Refine (Max ?).2 ? (UnifVar x (iota y));
        Refine EQsym SubstIdLeft;
Save flexFlexMax;


(***** flex-rigid unification ********************************************)

[m|Nat][x:Fin m][t:Term m];
Inductive [FlexRigid : {ma:Maybe (Ex (AList m))}SET] Constructors
  [frOK : {n|Nat}{sig:AList m n}{Msig:(Max (Unifies (iota x) t)).1 (sub sig)}
          FlexRigid (yes (pr n sig))]
  [frKO : {fail:Nothing (Unifies (iota x) t)}FlexRigid no];
Discharge m;

Goal {m|Nat}{x:Fin m}{t:Term m}Maybe (Ex (AList m));
Program flexRigid m x t;
  Program Elim (!Nat cases!) m;
    Program Elim (!Fin cases!) x;
      Program Abst fR2 n x (t' as (check x t));
        Program Elim (!Maybe cases!) t';
          Program Refine no;
          Program Refine yes (pr n (asnoc (anil n) t x));
Program Save;

Goal {m|Nat}{x|Fin m}{t|Term m}{ntx:(iota x == t)->FF}
     {ma|Maybe (Ex (AList m))}{mq:ma == flexRigid x t}
     FlexRigid x t ma;
Elim (!Nat cases!) m;
  Elim (!Fin cases!) x;
  AbstEq mu qu (check x t); Abst h (checkCheck qu); Elim (!Check elim!) h;
    Intros; Refine frOK;
      Refine (Max ?).2 ? UnifVar;
        Refine EQsym SubstIdLeft;
    Intros; Refine frKO;
      Refine NoUnifCycle;
        intros phere;
          Refine ntx;
            Qrepl Rew phere;
              Refine JMr;
Save flexRigidFlexRigid;

Freeze flexRigidFlexRigid;

(***** unification with accumulator **************************************)

[m,n|Nat][s,t:Term m][sig:AList m n];
Inductive [AMGU : {macc:Maybe (Ex (AList m))}SET] Constructors
  [amguOK : {o|Nat}{rho:AList n o}
            {max:(Max (Extends (Unifies s t) (sub sig))).1 (sub rho)}
            AMGU (yes (pr o (rho &a sig)))]
  [amguKO : {fail:Nothing (Extends (Unifies s t) (sub sig))}
            AMGU no];
Discharge m;

(***** useful properties of the relational spec *****)

Goal {m,n|Nat}{u|Term m}{x|Fin (suc m)}{s,t|Term (suc m)}{sig|AList m n}
     {macc|Maybe (Ex (AList m))}
     {H:AMGU ((u &for x) &mrt s) ((u &for x) &mrt t) sig macc}
     AMGU s t (asnoc sig u x)
          (may ([acc:Ex (AList m)]easnoc acc u x) &yam macc);
Elim (!AMGU elim!) H;
  Intros; Refine amguOK;
    Refine MaxResp UnifAccumulate; Immed;
  Intros; Refine amguKO;
    Refine NothingResp UnifAccumulate; Immed;
Save AMGUstep;

Goal {m|Nat}{x:Fin m}{t:Term m}{nxt:(iota x == t)->FF}
     AMGU (iota x) t anil (flexRigid x t);
AbstEq macc qacc (flexRigid x t); Abst h (flexRigidFlexRigid nxt qacc);
  Elim (!FlexRigid elim!) h;
  Intros; Refine amguOK;
    Refine MaxResp (EQUIVsym ExtendsId); Immed;
  Intros; Refine amguKO;
    Refine NothingResp (EQUIVsym ExtendsId); Immed;
Save AMGUflexRigid;

Goal {m,n|Nat}{s,t|Term m}{sig|AList m n}{macc|Maybe (Ex (AList m))}
     {H:AMGU s t sig macc}AMGU t s sig macc;
[Hint = EQrefl];
Elim (!AMGU elim!) H;
  Intros; Refine amguOK;
    Refine MaxResp (ExtendsResp UnifSym); Immed;
  Intros; Refine amguKO;
    Refine NothingResp (ExtendsResp UnifSym); Immed;
Save AMGUsym;


(***** and now the big program *****)

[step [m|Nat][u:Term m][x:Fin (suc m)]
      [amgu:{s,t:Term m}{acc:Ex (AList m)}Maybe (Ex (AList m))]
      [s,t:Term (suc m)][n|Nat][sig:AList m n]
    = may ([acc:Ex (AList m)]easnoc acc u x) &yam
           amgu (u &for x &mrt s) (u &for x &mrt t) (pr n sig)
];

Goal {m|Nat}{s,t:Term m}{acc:Ex (AList m)}Maybe (Ex (AList m));
Program amgu m s t acc;
  Program Elim (!Nat eduardo!) m;
    Program Elim (!Term elim!) s;
      Program Elim (!Ex cases!) acc;
        Program Elim (!AList cases!) b;
          Program Elim (!Term cases!) t;
            Program Names m y x;
              Program Refine yes (flexFlex x y);
              Next 22;
              Program Refine flexRigid i (leaf n);
              Next 23;
              Program Refine flexRigid i (s &fork t);
          Next 17;
          Program Names m n sig r j i t;
          Program Refine (Normal (step r j amgu (iota i) t sig));
      Next 10;
      Program Elim (!Term cases!) t;
        Program Elim (!Ex cases!) acc;
          Program Elim (!AList cases!) b;
            Program Refine flexRigid i (leaf n);
            Program Refine (Normal (step t x amgu leaf (iota i) sig));
          Program Refine yes acc;
          Program Refine no;
      Program Names m s1 t1 t;
        Program Elim (!Term cases!) t;
          Program Elim (!Ex cases!) acc;
            Program Elim (!AList cases!) b;
              Program Refine flexRigid i (s1 &fork t1);
              Program Refine
                (Normal (step t x amgu (s1 &fork t1) (iota i) sig));
          Program Refine no;
          Program Refine ([acc:Ex (AList m)]amgu t1 t acc) &yam amgu s1 s acc;
Program Save;


(***** and the big proof *****)

Goal {m,n|Nat}{s,t|Term m}{sig|AList m n}{macc|Maybe (Ex (AList m))}
     {q:macc == amgu s t (pr n sig)}AMGU s t sig macc;
Elim (!Nat eduardo!) m; AbstEq macc q (amgu s t (pr n sig));
  Elim (!Term elim!) s;
    Elim (!AList cases!) sig;
      Elim (!Term cases!) t;
        Names n y x; AbstEq acc qacc (flexFlex x y); Elim (!Ex cases!) acc;
          Intros; Refine amguOK; Refine flexFlexMax qacc;
        intros; Refine AMGUflexRigid; KJunify;
        intros; Refine AMGUflexRigid; KJunify;
      Intros _______ memo; Refine AMGUstep; Refine memo.2 JMr;
    Elim (!Term cases!) t;
      Elim (!AList cases!) sig;
        intros; Refine AMGUsym AMGUflexRigid; KJunify;
        intros ______ memo; Refine AMGUstep; Refine memo.2 JMr;
      Intros; Qrepl Rew (JMresp (pr n) (AListIdLeft sig));
        Refine amguOK; Refine UnifTriv;
      Intros; Refine amguKO; Normal; KJunify;
    Names m s1 t1 n t sig sh th memo; Elim (!Term cases!) t;
      Elim (!AList cases!) sig;
        intros; Refine AMGUsym AMGUflexRigid; KJunify;
        Intros; Refine AMGUstep; Refine memo.2 JMr;
      Intros; Refine amguKO; Normal; KJunify;
      AbstEq macc1 qacc1 (amgu s1 s (pr n sig)); Abst h (sh macc1 qacc1 memo);
        Elim (!AMGU elim!) h;
        AbstEq macc2 qacc2 (amgu t1 t (pr o (rho &a sig)));
          Abst h' (th macc2 qacc2 memo); Elim (!AMGU elim!) h';
            Intros m n sig o rho t t1 l tau maxt s s1 maxs _____;
              Qrepl Rew (JMsym (AListAssoc tau rho sig)); Refine amguOK;
                Refine (Max ?).2 (EQsym SubstAListComp);
                  Refine MaxResp (ExtendsResp UnifFork EQrefl);
                    Refine OptimistLemma UnifiesDClosed;
                      Refine +1 MaxResp
                        (ExtendsResp EQUIVrefl SubstAListComp); Immed;
            Intros; Refine amguKO;
              Refine NothingResp (ExtendsResp UnifFork EQrefl);
                Refine NothingRight; Immed;
                  Refine NothingResp (ExtendsResp EQUIVrefl SubstAListComp);
                    Immed;
          Intros; Refine amguKO;
            Refine NothingResp (ExtendsResp UnifFork EQrefl);
              Refine NothingLeft; Immed;
Save amguAMGU;
Freeze amguAMGU;


(***** the main program ****************************************************)

[m|Nat][s,t:Term m];
Inductive [MGU : {macc:Maybe (Ex (AList m))}SET] Constructors
  [mguOK : {n|Nat}{sig:AList m n}
           {max:(Max (Unifies s t)).1 (sub sig)}
           MGU (yes (pr n sig))]
  [mguKO : {fail:Nothing (Unifies s t)}
           MGU no];
Discharge m;

Goal {m|Nat}{s,t:Term m}Maybe (Ex (AList m));
Program mgu m s t;
  Program Refine amgu s t (pr m (anil m));
Program Save;

Goal {m|Nat}{s,t|Term m}{macc:Maybe (Ex (AList m))}
     {q:macc == mgu s t}MGU s t macc;
Expand mgu; Abst h (amguAMGU q); Elim (!AMGU elim!) h;
  intros; Refine mguOK;
    Refine MaxResp ExtendsId; Immed;
  intros; Refine mguKO;
    Refine NothingResp ExtendsId; Immed;
Save mguMGU;
Freeze mguMGU;


(***** some small examples ************************************************)

[v04 = iota (f0 (suc (suc (suc zero))))]
[v14 = iota (fs (f0  (suc (suc zero))))]
[v24 = iota (fs (fs  (f0  (suc zero))))]
[v34 = iota (fs (fs  (fs  (f0  zero))))];

(Normal (mgu (v04 &fork leaf) ((leaf &fork leaf) &fork v14)));
(Normal (mgu (v04 &fork leaf) ((leaf &fork leaf) &fork v04)));
(Normal (mgu (v04 &fork v14) ((leaf &fork v14) &fork (leaf &fork leaf))));
(Normal (mgu v04 (leaf &fork v04)));







