(***** Prelude **************************************************************)

[SET=Type]
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
Inductive [vect:nat->Type] Constructors
  [nil:vect zero]
  [op:: : {n|nat}{x:A}{xs:vect n}vect (suc n)];
Generate (!vect cases!);
Generate (!vect eduardo!);
Discharge A;
Configure Infix :: right 4;

Inductive [fin : nat->Type] Constructors
  [f0:{n:nat}fin (suc n)]
  [fs:{n|nat}{i:fin n}fin (suc n)];
Generate (!fin cases!);
Generate (!fin eduardo!);


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


(***** Basic Stuff *****************************************************)

(* + *)

Configure Infix + right 4;
Goal nat->nat->nat;
Program op+ x y;
  Program Elim (!nat elim!) x;
    Program Refine y;
    Program Refine suc (n + y);
Program Save;

(*************
[[n,y:nat]
   zero + y  ==>  y
|| suc n + y  ==>  suc (n + y)
]
**************)

Configure Infix << right 7;
Goal {n:nat}{m|nat}{i:fin m}fin (n + m);
Program op<< n m i;
  Program Elim (!nat elim!) n;
    Program Refine i;
    Program Refine fs (n << i);
Program Save;

(************
[[n:nat][m|nat][i:fin m]
   zero << i  ==>  i
|| suc n << i  ==>  fs (n << i)
]
*************)

Configure Infix @a right 4;
Goal {A|Type}{n,m|nat}{xs:vect A n}{ys:vect A m}vect A (n + m);
Program op@a A n m xs ys;
  Program Elim (!vect elim!) xs;
    Program Refine ys;
    Program Refine x :: (xs @a ys);
Program Save;

(************
[[A|Type][n|nat][x:A][xs:vect A n][m|nat][ys:vect A m]
    nil A @a ys  ==>  ys
|| (x :: xs) @a ys  ==>  x :: (xs @a ys)
]
*************)

[A?Type];
Inductive [Chop:{n|nat}{i:fin n}{xs:vect A n}Type] Constructors
  [unChop : {n,m|nat}{xs:vect A n}{a:A}{ys:vect A m}
            Chop (n << (f0 m)) (xs @a a :: ys)];
Generate (!Chop cases!);

Goal {n|nat}{i:fin n}{xs:vect A n}Chop i xs;
Program chop n i xs;
  Program Elim (!fin elim!) i;
    Program Elim (!vect cases!) xs;
      Program Refine unChop (nil A) x xs;
    Program Elim (!vect cases!) xs;
      Program Abst chopFs|n x xs i (c as chop i xs);
        Program Elim (!Chop cases!) c;
          Program Refine unChop (x :: xs) a ys;
Program Save;

(**********
[[n|nat][x:A][xs:vect A n][i:fin n]
   chop (f0 n) (x :: xs)  ==>  unChop (nil A) x xs
|| chop (fs i) (x :: xs)  ==>  chopFs x xs i (chop i xs)
]
[[n,m|nat][xs:vect A n][a:A][ys:vect A m][x:A]
   chopFs x (xs @a (a :: ys)) (n << f0 m) (unChop xs a ys)  ==>
    unChop (x :: xs) a ys
]
***********)

Discharge A;

(***** types *************************************************************)

Configure Infix >> right 6;
Inductive [type:Type] Constructors
  [O:type]
  [op>>:{S,T:type}type];
Generate (!type cases!);
Generate (!type eduardo!);

Goal {x,y:type}Type;
Program typeNoConfStmt x y;
  Program Elim (!type cases!) x;
    Program Elim (!type cases!) y;
      Program Refine {Phi:Type}Phi->Phi;
      Program Refine Absurd;
    Program Elim (!type cases!) y;
      Program Refine Absurd;
      Program Names S2 T2 S1 T1;
        Program Refine {Phi:Type}((S1 == S2)->(T1 == T2)->Phi)->Phi;
Program Save;
 
Goal {x,y:type}{q:x == y}{tg:Target q}typeNoConfStmt x y;
Program typeNoConf x y q tg;
  Program Elim (!JM elim!) q;
    Program Elim (!type cases!) x;
      Program Refine [Phi:Type][phi:Phi]phi;
      Program Refine [Phi:Type][phi:(S == S)->(T == T)->Phi]
                      phi (JMr S) (JMr T);
Program Save;  

Label (!type noConf!) typeNoConf;


Inductive [Not : type->Type] Constructors
  [notO : {S,T:type}Not O]
  [notAO : {S,T:type}Not (S >> T)]
  [notAl : {S|type}{S':Not S}{T1,T2:type}Not (S >> T1)]
  [notAr : {S:type}{T|type}{T':Not T}Not (S >> T)];

Configure Infix / right 7;
Goal {S:type}{S':Not S}type;
Program op/ S S';
  Program Elim (!Not elim!) S';
    Program Refine S >> T;
    Program Refine O;
    Program Refine S / S' >> T2;
    Program Refine S >> T / T';
Program Save;

(**********
[[S:type][T|type][T':Not T][S':Not S][T1,T2:type]
   O / notO S T  ==>  S >> T
|| (S >> T) / notAO S T  ==>  O
|| (S >> T1) / notAl S' T1 T2  ==>  (S / S') >> T2
|| (S >> T) / notAr S T'  ==>  S >> (T / T')
]
***********)

Inductive [TypeEq : {S,T:type}Type] Constructors
  [typeRefl : {T:type}TypeEq T T]
  [typeNot : {S|type}{S':Not S}TypeEq S (S / S')];
Generate (!TypeEq cases!);

Goal {S,T:type}TypeEq S T;
Program typeEq S T;
  Program Elim (!type elim!) S;
    Program Elim (!type cases!) T;
      Program Refine typeRefl O;
      Program Refine typeNot (notO S T);
    Program Names S1 T1 T;
      Program Elim (!type cases!) T;
        Program Refine typeNot (notAO S1 T1);
        Program Names S2 T2 S1 T1;
          Program Abst typeEqA S1 T1 S2 T2 (te1 as typeEq S1 S2)
                                           (te2 as typeEq T1 T2);
            Program Elim (!TypeEq cases!) te1;
              Program Names S T1 T2;
                Program Elim (!TypeEq cases!) te2;
                  Program Refine typeRefl (S >> T);
                  Program Names T T' S;
                    Program Refine typeNot (notAr S T');
Next 22;      Program Refine typeNot (notAl S' T1 T2);
Program Save;

(**************
[[S,T,S1,T1,S2,T2:type]
   typeEq (S1 >> T1) (S2 >> T2)  ==>
    typeEqA S1 T1 S2 T2 (typeEq S1 S2) (typeEq T1 T2)
|| typeEq (S1 >> T1) O  ==>  typeNot (notAO S1 T1)
|| typeEq O O  ==>  typeRefl O
|| typeEq O (S >> T)  ==>  typeNot (notO S T)
]
[[S|type][S':Not S][T1,T2:type][te2:TypeEq T1 T2][T:type][T':Not T]
   typeEqA S T S (T / T') (typeRefl S) (typeNot T')  ==>
    typeNot (notAr S T')
|| typeEqA S T S T (typeRefl S) (typeRefl T)  ==>  typeRefl (S >> T)
|| typeEqA S T1 (S / S') T2 (typeNot S') te2  ==>  typeNot (notAl S' T1 T2)
]
***************)

(***** terms *************************************************************)

Inductive [term : nat->Type] Constructors
  [var : {n|nat}{i:fin n}term n]
  [app : {n|nat}{f,a:term n}term n]
  [lam : {n|nat}{S:type}{t:term (suc n)}term n];

Inductive [wTerm : {n|nat}{G:vect type n}{T:type}Type] Constructors
  [wVar : {n,m|nat}{G:vect type n}{T:type}{D:vect type m}
          wTerm (G @a T :: D) T]
  [wApp : {n|nat}{G|vect type n}{S,T|type}
          {f:wTerm G (S >> T)}{a:wTerm G S}wTerm G T]
  [wLam : {n|nat}{G|vect type n}{S,T|type}
          {t:wTerm (S :: G) T}wTerm G (S >> T)];

Inductive [iTerm : {n|nat}{G:vect type n}Type] Constructors
  [iAppL : {n|nat}{G|vect type n}
           {f:iTerm G}{a:term n}iTerm G]
  [iAppO : {n|nat}{G|vect type n}
           {f:wTerm G O}{a:term n}iTerm G]
  [iAppR : {n|nat}{G|vect type n}{S,T|type}
           {f:wTerm G (S >> T)}{a:iTerm G}iTerm G]
  [iApp  : {n|nat}{G|vect type n}{S,T|type}{S'|Not S}
           {f:wTerm G (S >> T)}{a:wTerm G (S / S')}iTerm G]
  [iLam  : {n|nat}{G|vect type n}{S|type}
           {t:iTerm (S :: G)}iTerm G];

Goal {n|nat}{G|vect type n}{T:type}{w:wTerm G T}term n;
Program printW n G T w;
  Program Elim (!wTerm elim!) w;
    Program Refine var (n << (f0 m));
    Program Refine app (printW (S >> T) f) (printW S a);
    Program Refine lam S (printW T t);
Program Save;

(************
[[n|nat][G|vect type n][S,T|type][t:wTerm (S :: G) T][f:wTerm G (S >> T)]
 [a:wTerm G S][m|nat][D:vect type m]
   printW T (wVar G T D)  ==>  var (n << f0 m)
|| printW T (wApp f a)  ==>  app (printW (S >> T) f) (printW S a)
|| printW (S >> T) (wLam t)  ==>  lam S (printW T t)
]
**************)

Goal {n|nat}{G|vect type n}{i:iTerm G}term n;
Program printI n G i;
  Program Elim (!iTerm elim!) i;
    Program Refine app (printI f) a;
    Program Refine app (printW O f) a;
    Program Refine app (printW (S >> T) f) (printI a);
    Program Refine app (printW (S >> T) f) (printW (S / S') a);
    Program Refine lam S (printI t);
Program Save;

(*************
[[n|nat][G|vect type n][S|type][t:iTerm (S :: G)][T|type][S'|Not S]
 [f:wTerm G (S >> T)][a:wTerm G (S / S')][a'9:iTerm G][f'10:wTerm G O]
 [a'11:term n][f'12:iTerm G]
   printI (iAppL f'12 a'11)  ==>  app (printI f'12) a'11
|| printI (iAppO f'10 a'11)  ==>  app (printW O f'10) a'11
|| printI (iAppR f a'9)  ==>  app (printW (S >> T) f) (printI a'9)
|| printI (iApp f a)  ==>  app (printW (S >> T) f) (printW (S / S') a)
|| printI (iLam t)  ==>  lam S (printI t)
]
**************)

(***** typechecker ********************************************************)

Inductive [Check : {n|nat}{G:vect type n}{t:term n}Type] Constructors
  [wellTyped : {n|nat}{G|vect type n}{T:type}{w:wTerm G T}
               Check G (printW T w)]
  [illTyped : {n|nat}{G|vect type n}{i:iTerm G}
               Check G (printI i)];
Generate (!Check cases!);

Goal {n|nat}{G:vect type n}{t:term n}Check G t;
Program check n G t;
  Program Elim (!term elim!) t;
    Program Abst checkVar n i G (c as chop i G);
      Program Elim (!Chop cases!) c;
        Program Refine wellTyped a (wVar xs a ys);
    Program Abst checkApp n G f a (cf as check G f) (ca as check G a);
      Program Elim (!Check cases!) cf;
        Program Elim (!type cases!) T;
          Program Refine illTyped (iAppO w a);
          Program Elim (!Check cases!) ca;
            Program Names n G A wa S T wf;
              Program Abst checkWTApp n G wf wa (teq as typeEq S A);
                Program Elim (!TypeEq cases!) teq;
                  Program Names S n G T wf wa;
                    Program Refine wellTyped T (wApp wf wa);
Next 36;          Program Names S S' n G T wf wa;
                    Program Refine illTyped (iApp wf wa);
Next 29;    Program Refine illTyped (iAppR w i);
Next 21;
        Program Refine illTyped (iAppL i a);
Next 9;
    Program Abst checkLam n G S t (ct as check (S :: G) t);
      Program Elim (!Check cases!) ct;
        Program Refine wellTyped (S >> T) (wLam w);
        Program Refine illTyped (iLam i);
Program Save;

(*************
[[n|nat][S:type][t:term (suc n)][G:vect type n][f,a:term n][i:fin n]
   check G (var i)  ==>  checkVar n i G (chop i G)
|| check G (app f a)  ==>  checkApp n G f a (check G f) (check G a)
|| check G (lam S t)  ==>  checkLam n G S t (check (S :: G) t)
]
[[n,m|nat][xs:vect type n][a:type][ys:vect type m]
   checkVar (n + suc m) (n << f0 m) (xs @a (a :: ys)) (unChop xs a ys)  ==>
    wellTyped a (wVar xs a ys)
]
[[n|nat][G|vect type n][i:iTerm G][a:term n][ca:Check G a][S,T:type]
 [w:wTerm G (S >> T)][w'9:wTerm G O][A:type][wa:wTerm G A]
 [wf:wTerm G (S >> T)]
   checkApp n G (printW (S >> T) wf) (printW A wa) (wellTyped (S >> T) wf)
     (wellTyped A wa)  ==>  checkWTApp n G wf wa (typeEq S A)
|| checkApp n G (printW O w'9) a (wellTyped O w'9) ca  ==>
   illTyped (iAppO w'9 a)
|| checkApp n G (printW (S >> T) w) (printI i) (wellTyped (S >> T) w)
    (illTyped i)  ==>  illTyped (iAppR w i)
|| checkApp n G (printI i) a (illTyped i) ca  ==>  illTyped (iAppL i a)
]
[[S:type][n:nat][G:vect type n][T|type][wf:wTerm G (S >> T)][wa:wTerm G S]
 [S':Not S][wa'8:wTerm G (S / S')]
   checkWTApp n G wf wa'8 (typeNot S')  ==>  illTyped (iApp wf wa'8)
|| checkWTApp n G wf wa (typeRefl S)  ==>  wellTyped T (wApp wf wa)
]
[[n:nat][G:vect type n][S:type][i:iTerm (S :: G)][T:type][w:wTerm (S :: G) T]
   checkLam n G S (printW T w) (wellTyped T w)  ==>
    wellTyped (S >> T) (wLam w)
|| checkLam n G S (printI i) (illTyped i)  ==>  illTyped (iLam i)
]
**************)

check (nil type) (lam O (var (f0 zero)));
check (nil type) (app (lam O (var (f0 zero))) (lam O (var (f0 zero))));
check (nil type) (app (lam (O >> O) (var (f0 zero))) (lam O (var (f0 zero))));
