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

Generate (!Eq sym!);

[trueProp = {P:Prop}P->P];
[trueProof = [P:Prop][p:P]p : trueProp];

Label (!any inhabited type!) trueProp;
Label (!any inhabited type term!) trueProof;

(***** Some Datatypes ******************************************************)

Inductive [Empty : Type] Constructors;

Inductive [Unit  : Type] Constructors [void : Unit];
Label (!unit!) Unit;
Label (!unit void!) void;

Inductive [Bool  : Type] Constructors [true : Bool][false : Bool];
Generate (!Bool cases!);

Inductive [Nat : Type] Constructors
  [zero : Nat]
  [suc  : {n:Nat}Nat];
Generate (!Nat cases!);
Generate (!Nat eduardo!);
Label (!nat!) Nat;
Label (!nat zero!) zero;
Label (!nat suc!) suc;

(****** No Confusion Theorems ***********************************************)

[Absurd = {T:Type}T];

Goal {x,y:Bool}Type;
Program BoolNoConfStmt x y;
  Program Elim (!Bool cases!) x;
    Program Elim (!Bool cases!) y;
      Program Refine {Phi:Type}Phi->Phi;
      Program Refine Absurd;
    Program Elim (!Bool cases!) y;
      Program Refine Absurd;
      Program Names y x;
        Program Refine {Phi:Type}Phi->Phi;
Program Save;

Goal {x,y:Bool}{q:x == y}{tg:Target q}BoolNoConfStmt x y;
Program BoolNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!Bool cases!) x;
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:Phi]phi;
Program Save;

Label (!Bool noConf!) BoolNoConf;

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

(***** LLB *****)

Goal Nat -> Nat -> Nat;
Names x y;
Elim (!Nat elim!) x;
KillRef;

[Plus = [x,y:Nat]Nat];

Goal {x,y:Nat}Plus x y;
Elim (!Nat elim!) x;
  Intros; Refine y;
  Intros x xh y;
    Refine suc (xh y);
Save plus;


(***** Simple Examples *****************************************************)

(* + *)

Configure Infix + right 4;

Goal Nat->Nat->Nat;
Program op+ x y;
  Program Elim (!Nat elim!) x;
    Program Refine y;
    Program Refine suc (n + y);
Program Save;

op+;
Unfreeze op+;
op+;
Freeze op+;

(* fib *)

Goal Nat->Nat;
Program fib n;
  Program Elim (!Nat eduardo!) n;
    Program Elim (!Nat cases!) z;
      Program Refine zero;
      Program Elim (!Nat cases!) n;
        Program Refine suc zero;
        Program Refine (fib n) + (fib (suc n));
Program Save;


(***** Some Inductive Families *********************************************)

[A?Type];
Inductive [Vect:Nat->Type] Constructors
  [vnil:Vect zero]
  [vcons:{n|Nat}{x:A}{xs:Vect n}Vect (suc n)];

Generate (!Vect cases!);
Generate (!Vect eduardo!);
Discharge A;

(***** examples *************************************************************)

Goal {n|Nat}{xs,ys:Vect Nat n}Vect Nat n;
Program vplus n xs ys;
  Program Elim (!Vect elim!) xs;
    Program Elim (!Vect cases!) ys;
      Program Refine vnil;
    Program Elim (!Vect cases!) ys;
      Program Names n y ys x xs ;
        Program Refine vcons (x + y) (vplus xs ys);
Program Save;


(***** views ****************************************************************)

Inductive [Compare:{x,y:Nat}Type] Constructors
  [CompLess : {x,y:Nat}Compare x (x + (suc y))]
  [CompEq : {x:Nat}Compare x x]
  [CompMore : {x,y:Nat}Compare (y + (suc x)) y];
Generate (!Compare cases!);

Goal {x,y:Nat}Compare x y;
Program compare x y;
  Program Elim (!Nat elim!) x;
    Program Elim (!Nat cases!) y;
      Program Refine CompEq zero;
      Program Refine CompLess zero n;
    Program Elim (!Nat cases!) y;
      Program Refine CompMore n zero;
      Program Names y x;
        Program Abst compSuc x y (c as compare x y);
          Program Elim Compare_elim c;
            Program Refine CompLess (suc x) y;
            Program Refine CompEq (suc x);
            Program Refine CompMore x (suc y);
Program Save;


Goal Nat->Nat->Nat;
Program max x y;
  Program Abst max2 x y (c as compare x y);
    Program Elim (!Compare cases!) c;
      Program Refine x + (suc y);
      Program Refine x;
      Program Refine y + (suc x);
Program Save;


(***** a recursive view ******)

Inductive [PNat : Nat -> Type] Constructors
  [mkPNat : {n:Nat}{pn:{x,y|Nat}{q:n == suc (x + y)}PNat y}PNat n];

Goal {n:Nat}{x,y:Nat}(n == suc (x + y))->PNat y;
Program pNatHelp n x y q;
  Program Elim (!Nat elim!) n;
    Program Elim (!Nat cases!) x;
      Program Refine mkPNat y ([x,z|Nat][q:y == suc (x + z)]
                              pNatHelp y x z q);
      Program Refine pNatHelp (suc (n + y)) n y JMr;
Program Save;

Goal {n:Nat}PNat n;
Program pNat n; 
  Program Refine mkPNat n ([x,y|Nat]pNatHelp n x y);
Program Save;

Goal view_pNat : {n:Nat}{P:Nat->Type}
                  {p:{m:Nat}{pm:{x,y|Nat}{q:m == suc (x + y)}P y}P m}P n;
intros n' P p; Abst n n';
  Abst pn (pNat n);
    Elim (!PNat elim!) pn;
      intros;
        Refine p;
          Immed;
Save;

Goal Nat -> Nat -> Nat;
Program gcd x y;
  Program Elim view_pNat x;
    Program Elim view_pNat y;
      Program Names y x;
        Program Abst gcd2 x y (cxy as compare x y);
          Program Elim (!Compare cases!) cxy;
            Program Elim (!Nat cases!) x;
              Program Refine (suc y);
(*              Program Refine gcd (suc n) (suc y); *)
(* instead *)   Intros x y yh xh;
                  Refine ret_gcd2; Refine call_gcd;
                    Refine -0 yh JMr;
                      Immed;
            Next 15; Program;
              Program Refine x;
            Program Elim (!Nat cases!) y;
              Program Refine (suc x);
(*              Program Refine gcd (suc x) (suc n); *)
(* instead *)   Intros y x yh xh;
                  Refine ret_gcd2; Refine call_gcd|(suc x)|(suc y);
                    Refine -0 xh JMr;
Program;
Program Save;

(Normal (gcd (!42!) (!35!)));

(Normal (gcd (fib (!15!)) (fib (!16!))));
