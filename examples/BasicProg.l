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

Inductive [empty : Type] Constructors;
Inductive [unit  : Type] Constructors [void : unit];
Inductive [bool  : Type] Constructors [true : bool][false : bool];
Generate (!bool cases!);

Inductive [nat : Type] Constructors
  [zero : nat]
  [suc  : {n:nat}nat];
Generate (!nat cases!);
Generate (!nat eduardo!);

[A?Type];
Inductive [list:Type] Constructors
  [nil:list]
  [op:: : {x:A}{xs:list}list];
Generate (!list cases!);
Generate (!list eduardo!);
Discharge A;
Configure Infix :: right 4;

(***** Simple Examples *****************************************************)

(* + *)

Configure Infix + right 4;

Goal nat->nat->nat;
Program op+ x y;
  Program Elim (!nat elim!) x;
    Program Refine y;
    Program Refine suc (n + y);
Program Save;


(* fib *)

Goal nat->nat;
Program fib n;
  Program Elim (!nat eduardo!) n;
    Program Elim (!nat cases!) z;
      Program Refine zero;
      Program Elim (!nat cases!) n;
        Program Refine suc zero;
        Program Refine (fib n) + (fib (suc n));
Program Save;


(* le *)

Configure Infix &le left 3;

Goal nat->nat->bool;
Program op&le x y;
  Program Elim (!nat eduardo!) x;
    Program Elim (!nat cases!) z;
      Program Refine true;
      Program Elim (!nat cases!) y;
        Program Refine false;
        Program Names y x;
          Program Refine x &le y;
Program Save;


(* eq *)

Configure Infix &eq left 3;

Goal nat->nat->bool;
Program op&eq x y;
  Program Elim (!nat eduardo!) x;
    Program Elim (!nat cases!) z;
      Program Elim (!nat cases!) y;
        Program Refine true;
        Program Refine false;
      Program Elim (!nat cases!) y;
        Program Refine false;
        Program Names y x;
          Program Refine x &eq y;
Program Save;


(***** Berry's example rephrased *******************************************)

Goal bool->bool->bool->bool;
Program majority x y z;
  Program Elim (!bool cases!) x;
    Program Elim (!bool cases!) y;
      Program Refine true;
      Program Refine z;
    Program Elim (!bool cases!) y;
      Program Refine z;
      Program Refine false;
Program Save;


(***** The decision tree can acquire more information **********************)

Goal nat->(list nat)->bool;
Program member n xs;
  Program Elim (!list eduardo!) xs;
    Program Elim (!list cases!) z;
      Program Refine false;
      Program Abst member2 n x xs (b as n &eq x);
        Program Elim (!bool cases!) b;
          Program Refine true;
          Program Refine member n xs;
Program Save;


(***** Some Inductive Families *********************************************)

Inductive [so : bool -> Type] Constructors
  [oh : so true];
Generate (!so cases!);

[A?Type];
Inductive [vect:nat->Type] Constructors
  [vnil:vect zero]
  [vcons:{n|nat}{x:A}{xs:vect n}vect (suc n)];
Generate (!vect cases!);
Generate (!vect eduardo!);
Discharge A;



(* and sigma types *)

[A|Type][B:A->Type];
Inductive [ex : Type] Constructors
  [wit:{a:A}{b:B a}ex];
Discharge A;
Generate (!ex cases!);


(****** No Confusion Theorems ***********************************************)

[Absurd = {T:Type}T];

Goal {x,y:nat}Type;
Program natNoConfStmt x y;
  Program Elim (!nat cases!) x;
    Program Elim (!nat cases!) y;
      Program Refine {Phi:Type}Phi->Phi;
      Program Refine Absurd;
    Program Elim (!nat cases!) y;
      Program Refine Absurd;
      Program Names y x;
        Program Refine {Phi:Type}((x == y)->Phi)->Phi;
Program Save;
 
Goal {x,y:nat}{q:x == y}{tg:Target q}natNoConfStmt x y;
Program natNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!nat cases!) x;
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:(n == n)->Phi]phi (JMr n);
Program Save;  

Label (!nat noConf!) natNoConf;

Goal {x,y:bool}Type;
Program boolNoConfStmt x y;
  Program Elim (!bool cases!) x;
    Program Elim (!bool cases!) y;
      Program Refine {Phi:Type}Phi->Phi;
      Program Refine Absurd;
    Program Elim (!bool cases!) y;
      Program Refine Absurd;
      Program Names y x;
        Program Refine {Phi:Type}Phi->Phi;
Program Save;

Goal {x,y:bool}{q:x == y}{tg:Target q}boolNoConfStmt x y;
Program boolNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!bool cases!) x;
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:Phi]phi;
Program Save;

Label (!bool noConf!) boolNoConf;


(***** a classic ************************************************************)

Goal {A|Type}{n:nat}{xs:vect A (suc n)}vect A n;
Program vtail A n xs;
  Program Elim (!vect cases!) xs;
    Program Refine xs;
Program Save;

Goal {n|nat}{xs,ys:vect nat n}vect nat n;
Program vplus n xs ys;
  Program Elim (!vect elim!) xs;
    Program Elim (!vect cases!) ys;
      Program Refine vnil;
    Program Elim (!vect cases!) ys;
      Program Names n y ys x xs ;
        Program Refine vcons (x + y) (vplus xs ys);
Program Save;

(***** where it pays to pull stuff to the left ******************************)

Goal {A|Type}nat->(list (ex [n:nat]A))->bool;
Program occ A y xas;
  Program Elim (!list elim!) xas;
    Program Refine false;
    Program Elim (!ex cases!) x;
    Program Abst occ2 y a b xs (q as a &eq y);
      Program Elim (!bool cases!) q;
        Program Refine true;
        Program Refine occ y xs;
Program Save;

Goal {A|Type}{n:nat}{xas:list (ex [n:nat]A)}(so (occ n xas))->A;
Program Proj A n xas pf;
  Program Elim (!list elim!) xas;
    Program Elim (!so cases!) pf;
    Program Elim (!ex cases!) x;
      Program Abst Proj2|A n a b xs (q as a &eq n) pf;
        Program Elim (!bool cases!) q;
          Program Refine b;
          Program Refine Proj n xs pf;
Program Save;

