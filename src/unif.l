Load lib_finite;

(*************************************************************************)
(********                                                         ********)
(********        Miscellaneous Preliminary Things                 ********)
(********                                                         ********)
(*************************************************************************)

Configure Infix &o right 4;
Goal COMPOSE : <op&o:{R,S,T|Type}(S->T)->(R->S)->(R->T)>
               {R,S,T|Type}{f:S->T}{g:R->S}{r:R}Eq ((f &o g) r) (f (g r));
Dale;
SaveReductions op&o;

[Absurd = {A|Type}A];
[Neq = [T|Type][x,y:T](Eq x y)->Absurd];

Goal Neq_sym : {T|Type}{x,y|T}(Neq x y)->Neq y x;
Intros T x y xny yqx;
  Refine xny (Eq_sym yqx);
Save;

(*************************************************************************)
(********                                                         ********)
(********        Finite Set Equality Test                         ********)
(********                                                         ********)
(*************************************************************************)

Configure Infix &E right 3;
Goal FINEQ : <op&E:{n|nat}{x,y:fin n}bool>
             <e1:{n|nat}Eq ((f_zero n) &E (f_zero n)) true>
             <e2:{n|nat}{y:fin n}Eq ((f_zero n) &E (f_suc y)) false>
             <e3:{n|nat}{x:fin n}Eq ((f_suc x) &E (f_zero n)) false>
             {n|nat}{x,y:fin n}Eq ((f_suc x) &E (f_suc y)) (x &E y);
Eduardo x Then Eduardo y Then Dale;
SaveReductions op&E;

Goal fineq_cases : {n|nat}{x,y:fin n}
                   {Phi:{b:bool}Type}
                   {phi_q:(Eq x y)->Phi true}
                   {phi_n:(Neq x y)->Phi false}
                   Phi (x &E y);
Induction x Then Cases y;
  intros; Refine phi_q (Eq_refl ?);
  intros;
    Refine phi_n;
      Expand Neq; KJunify;
  intros;
    Refine phi_n;
      Expand Neq; KJunify;
  intros n y x x_hyp Phi phi_q phi_n;
    Refine x_hyp;
      intros; Refine phi_q;
        Refine Eq_resp; Immed;
      intros xNy;
        Refine phi_n;
          Expand Neq; KJunify;
            intros xQy; Refine xNy xQy;
Save;

Goal fineq_lemma : {n|nat}{i:fin n}Eq (i &E i) true;
intros;
  Refine fineq_cases ? ? ([H:bool]Eq H true);
    intros; Refine Eq_refl;
    intros bad; Refine bad (Eq_refl ?);
Save;

Goal fineq_not_lemma : {n|nat}{i,j:fin n}(Neq i j)->Eq (i &E j) false;
intros n i j;
  Refine fineq_cases ? ? ([H:bool](Neq i j)->Eq H false);
    intros ugly bad; Refine bad ugly;
    intros; Refine Eq_refl;
Save;

Goal IF : <if:{T|Type}{b:bool}{tT,fT:T}T>
          <e1:{T|Type}{tT,fT:T}Eq (if true tT fT) tT>
          {T|Type}{tT,fT:T}Eq (if false tT fT) fT;
Eduardo b Then Dale;
SaveReductions if;

Goal if_cases : {T|Type}{b:bool}{tT,fT:T}
                {Phi:T->Type}
                {phi_t:(Eq b true)->Phi tT}
                {phi_f:(Eq b false)->Phi fT}
                Phi (if b tT fT);
Cases b;
  intros; Refine phi_t (Eq_refl ?);
  intros; Refine phi_f (Eq_refl ?);
Save;

Goal who_cares_lemma : {T|Type}{b:bool}{t:T}Eq (if b t t) t;
Cases b Then intros Then Refine Eq_refl;
Save;



(*************************************************************************)
(********                                                         ********)
(********        Concrete Category Things                         ********)
(********                                                         ********)
(*************************************************************************)

Record [ARROW:Type] Fields
  [Index : Type]
  [Obj : Index->Type]
  [Arrow : {n,m:Index}Type]
  [App : {n,m|Index}{S:Arrow n m}{t:Obj m}Obj n]
  [Iota : {n:Index}Arrow n n]
  [Comp : {n,m,l|Index}{T:Arrow n m}{S:Arrow m l}Arrow n l]
  [IotaApp : {n|Index}{t:Obj n}Eq (App (Iota n) t) t]
  [CompApp : {n,m,l|Index}{T:Arrow n m}{S:Arrow m l}{t:Obj l}
             Eq (App (Comp T S) t) (App T (App S t))];
Configure Memo ARROW ARROW;
Configure Memo ARROW elim ARROW_elim;

[S:ARROW];

Configure Infix >> right 2;
Configure Infix << left 4;
Configure Infix * right 3;
$[N = Index S];
$[O = Obj S];
$[op<< = Arrow S];
$[op>> = App S];
$[I    = Iota S];
$[op*  = Comp S];

Configure Infix &q right 3;
$[op&q = [n,m|N][f,g:m << n]{t:O n}Eq (f >> t) (g >> t)];

Record [Closed:Type] Parameters [n:N] Fields
  [Why : {m|N}(m << n)->Type]
  [Ext : {m|N}{f,g|m << n}
         (f &q g)->(Why f)->Why g]
  [Also : {l,m|N}{f:l << m}{g:m << n}(Why g)->Why (f * g)];
Discharge n ?;
Configure Memo Closed Closed;
Configure Memo Closed elim Closed_elim;

Record [Maximal:Type] Parameters [m,n|N][P:Closed n][f:m << n]
Fields
  [Holds : Why P f]
  [Factor : {l|N}{g|l << n}(Why P g)-><h:(l << m)>(g &q (h * f))];
Discharge m ?;
Configure Memo Maximal Maximal;
Configure Memo Maximal elim Maximal_elim;

$Goal qrefl : {n,m|N}{f:m << n}(f &q f);
Intros; Refine Eq_refl;
Save;

$Goal qsym : {n,m|N}{f,g|m << n}(f &q g)->(g &q f);
Intros; Refine Eq_sym; Immed;
Save;

$Goal qtrans : {n,m|N}{f,g,h|n << m}(f &q g)->(g &q h)->(f &q h);
Intros; Refine Eq_trans; Immed;
Save;

Goal Left_Id : {n,m|N}{f:n << m}(((I n) * f) &q f);
Wave > (CompApp,IotaApp);
intros; Refine Eq_refl;
Save;

Goal Right_Id : {n,m|N}{f:n << m}((f * (I m)) &q f);
Wave > (CompApp,IotaApp);
intros; Refine Eq_refl;
Save;

Goal Assoc : {n,m,l,k|N}{f:n << m}{g:m << l}{h:l << k}
             (((f * g) * h) &q (f * (g * h)));
Wave > CompApp;
intros; Refine Eq_refl;
Save;

Goal AND : {n|N}(Closed n)->(Closed n)->Closed n;
intros n; Induction 1; intros P PX PC; Induction 1; intros Q QX QC;
  Refine make_Closed;
    intros m s;
      Refine (P s)#(Q s);
    Dnf; intros m f g fqg hyp;
      Refine (PX fqg hyp.1,QX fqg hyp.2);
    Dnf; intros l m f g hyp;
      Refine (PC f g hyp.1,QC f g hyp.2);
Save;
Configure Infix &A right 2;
$[op&A = AND];

Goal BOUND : {n,m|N}{b:n << m}(Closed m)->(Closed n);
intros n m b; Induction 1; intros P PX PC; Refine make_Closed;
  intros l f;
    Refine P (f * b);
  Dnf; intros k f g fqg hyp;
    Refine PX;
      Refine f * b;
      Wave > (CompApp,fqg);
        intros; Refine Eq_refl;
      Immed;
  Dnf; intros l k f g hyp;
    Refine PX;
      Next +1; Wave > Assoc;
        intros; Refine Eq_refl;
      Refine PC;
        Refine hyp;
Save;
Configure Infix &b right 3;
$[op&b = BOUND];

[EQUIV [n|N][P,Q:Closed n] = {m|N}{f:m << n}((Why P f)->(Why Q f))#
                                               (Why Q f)->(Why P f)];

Goal EquivMax : {n|N}{P,Q|Closed n}{equiv:EQUIV P Q}{m|N}{g:m << n}
                {gP:Maximal P g}Maximal Q g;
intros n P Q equiv m g; Induction 1; intros holds fac;
Refine make_Maximal;
  Refine (equiv g).1; Refine holds;
  intros l h qh; Intros#;
    Refine (fac|l|h ?).1;
      Refine (equiv h).2; Immed;
  Intros t; Dnf; Refine (fac ((equiv h).2 qh)).2;
Save;

Goal Greedy : {n,m,l|N}{P,Q|Closed l}{f|n << m}{g|m << l}
              {gMax:Maximal P g}{fMax:Maximal (g &b Q) f}
              Maximal (P &A Q) (f * g);
intros ___;
Induction P; intros P PX PC;
Induction Q; intros Q QX QC;
intros __;
Induction gMax; Expand Why;
intros Pg gFac;
Induction fMax; Expand Why;
intros gQf fFac;
Refine make_Maximal;
  Intros#;
    Refine PC;
      Immed;
  intros k h PQh; Intros#;
    Refine (fFac|?|(gFac|?|h ?).1 ?).1;
      Refine PQh.1;
      Refine QX;
        Refine +1 (gFac ?).2;
      Refine PQh.2;
    Wave < Assoc;
    Wave 1 > CompApp;
    Wave < (fFac (QX (gFac PQh.1).2 PQh.2)).2;
    Wave < CompApp;
    Wave < (gFac PQh.1).2;
      intros; Refine Eq_refl;
Save;

Goal UNIFIER : {n|N}{s,t:O n}Closed n;
intros n s t;
  Refine make_Closed;
    intros m f;
      Refine Eq (f >> s) (f >> t);
    Dnf; intros n f g fQg hyp;
      Wave < fQg;
        Immed;
    Dnf; intros l m f g hyp;
      Wave > (CompApp,hyp);
        Refine Eq_refl;
Save;

Goal UNIFIER_SYM : {n|N}{s,t:O n}EQUIV (UNIFIER s t) (UNIFIER t s);
Expand EQUIV Why; intros _____; Intros# Then Refine Eq_sym;
Save;

[Inj [S,T|Type][f:S->T] = {x,y|S}(Eq (f x) (f y))->Eq x y];

Goal UNIFIER_INJ : {f:{n|N}(O n)->O n}
                   {inj:{n|N}Inj (f|n)}
                   {comm:{m,n|N}{g:m << n}{x:O n}Eq (g >> f x) (f (g >> x))}
                   {n|N}{s,t:O n}EQUIV (UNIFIER s t) (UNIFIER (f s) (f t));
Expand EQUIV Why Inj; intros f inj comm n s t m g; Intros#;
  intros hyp; Wave 3 > (comm,hyp); Refine Eq_refl;
  intros hyp; Refine inj; Wave 2 < comm; Immed;
Save;

[Inj2 [S1,S2,T|Type][f:S1->S2->T] =
      {x1,y1|S1}{x2,y2|S2}(Eq (f x1 x2) (f y1 y2))->(Eq x1 y1)#(Eq x2 y2)];

Goal UNIFIER_INJ2 : {f:{n|N}(O n)->(O n)->O n}
                    {inj:{n|N}Inj2 (f|n)}
                    {comm:{m,n|N}{g:m << n}{x,y:O n}
                          Eq (g >> f x y) (f (g >> x) (g >> y))}
                    {n|N}{s1,t1,s2,t2:O n}
                    EQUIV ((UNIFIER s1 s2) &A (UNIFIER t1 t2))
                          (UNIFIER (f s1 t1) (f s2 t2));
Expand EQUIV Why Inj2; intros f inj comm n s1 t1 s2 t2 m g; Intros#;
  intros hyp; Wave 5 > (comm,hyp); Refine Eq_refl;
  intros hyp; Refine inj; Wave 2 < comm; Immed;
Save;

Goal MaxBoundUnifier : {m,n|N}{b|m << n}{s,t|O n}{l|N}{u|l << m}
                       {max:Maximal (UNIFIER (b >> s) (b >> t)) u}
                       Maximal (BOUND b (UNIFIER s t)) u;
intros _______; Induction 1; intros holds fac;
Refine make_Maximal;
  Expand Why; Wave 2 > CompApp; Refine holds;
  intros k g w; Intros#;
    Refine (fac|?|g ?).1;
      Expand Why; Wave 2 < CompApp; Refine w;
  intros; Refine (fac ?).2;
Save;

Discharge S ?;

(*************************************************************************)
(********                                                         ********)
(********        Option Type and Monadic Things                   ********)
(********                                                         ********)
(*************************************************************************)

Inductive [opt:Type] Parameters [T:Type] Theorems
Constructors
[some : T->opt]
[none : opt];
Discharge T ?;

Goal SWITCH : <sw:{S,T|Type}{yes:S->T}{no:T}{x:opt S}T>
              <e1:{S,T|Type}{yes:S->T}{no:T}{s:S}
                  Eq (sw yes no (some s)) (yes s)>
              {S,T|Type}{yes:S->T}{no:T}
                  Eq (sw yes no (none S)) no;
Eduardo x Then Dale;
SaveReductions switch;

Goal switch_cases : {S,T|Type}{yes:S->T}{no:T}{x:opt S}{Phi:T->Type}
                    {phi_s:{s:S}(Eq x (some s))->Phi (yes s)}
                    {phi_n:(Eq x (none S))->Phi no}
                    Phi (switch yes no x);
Cases x;
  intros; Refine phi_s ? (Eq_refl ?);
  intros; Refine phi_n (Eq_refl ?);
Save;

Goal TRY2 : <try2 : {R,S,T|Type}{f:R->S->T}{r:opt R}{s:opt S}opt T>
            <e1:{R,S,T|Type}{f:R->S->T}{r:R}{s:S}
            Eq (try2 f (some r) (some s)) (some (f r s))>
            <e2:{R,S,T|Type}{f:R->S->T}{r:R}
            Eq (try2 f (some r) (none S)) (none T)>
            {R,S,T|Type}{f:R->S->T}{s:opt S}
            Eq (try2 f (none R) s) (none T);
Eduardo r;
  Eduardo s Then Dale;
  Dale;
SaveReductions try2;

Goal try2_lemma : {R,S,T|Type}{f:R->S->T}{r:opt R}
                  Eq (try2 f r (none S)) (none T);
Cases min r Then intros Then Refine Eq_refl;
Save;

Goal try2_cases : {R,S,T|Type}{f:R->S->T}{r:opt R}{s:opt S}
                  {Phi:(opt T)->Type}
                  {phi_y : {r':R}{s':S}(Eq r (some r'))->(Eq s (some s'))->
                           Phi (some (f r' s'))}
                  {phi_n1 : (Eq r (none R))->Phi (none T)}
                  {phi_n2 : (Eq s (none S))->Phi (none T)}
                  Phi (try2 f r s);
Cases min r;
  Cases min s;
    intros ____ r s ____;
      Refine phi_y ? ? (Eq_refl ?) (Eq_refl ?);
    intros ____ r ____;
      Refine phi_n2 (Eq_refl ?);
  intros ____ s ____;
    Refine phi_n1 (Eq_refl ?);
Save;

(*************************************************************************)
(********                                                         ********)
(********        ML Syntax And Occurrence Things                  ********)
(********                                                         ********)
(*************************************************************************)

[n:nat];

Configure Infix - right 4;
Inductive [ml:Type] Theorems
Constructors
[V : (fin n)->ml]
[op- : ml->ml->ml];

Configure Infix &l left 3;
Configure Infix &r right 3;
Inductive [ml_occur:Type] Theorems
Constructors
[here : ml_occur]
[op&l : ml_occur -> ml -> ml_occur]
[op&r : ml -> ml_occur -> ml_occur];

Discharge n ?;

Goal ml_zero_empty : {x:ml zero}Absurd;
Induction x;
  Cases 1;
  intros ____; Immed;
Save;

Configure Infix &p right 2;
Goal PUSH : <op&p:{m,n|nat}{f:(fin n)->ml m}{t:ml n}ml m>
            <e1:{m,n|nat}{f:(fin n)->(ml m)}{i:fin n}
                Eq (f &p (V i)) (f i)>
            {m,n|nat}{f:(fin n)->(ml m)}{s,t:ml n}
                Eq (f &p (s - t)) ((f &p s) - (f &p t));
Eduardo t Then Dale;
SaveReductions op&p;

Goal OCPUSH : <ocpush:{m,n|nat}{f:(fin n)->ml m}{oc:ml_occur n}ml_occur m>
              <e1:{m,n|nat}{f:(fin n)->ml m}Eq (ocpush f (here n)) (here m)>
              <e2:{m,n|nat}{f:(fin n)->ml m}{l:ml_occur n}{r:ml n}
                  Eq (ocpush f (l &l r)) ((ocpush f l) &l (f &p r))>
              {m,n|nat}{f:(fin n)->ml m}{l:ml n}{r:ml_occur n}
                  Eq (ocpush f (l &r r)) ((f &p l) &r (ocpush f r));
Eduardo oc Then Dale;
SaveReductions ocpush;

Goal OCPUT : <ocput:{n|nat}{oc:ml_occur n}{t:ml n}ml n>
             <e1:{n|nat}{t:ml n}Eq (ocput (here n) t) t>
             <e2:{n|nat}{l:ml_occur n}{r:ml n}{t:ml n}
                 Eq (ocput (l &l r) t) ((ocput l t) - r)>
             {n|nat}{l:ml n}{r:ml_occur n}{t:ml n}
                 Eq (ocput (l &r r) t) (l - (ocput r t));
Eduardo oc Then Dale;
SaveReductions ocput;

Goal ocpush_lemma : {m,n|nat}{f:(fin n)->ml m}{oc:ml_occur n}{t:ml n}
                    Eq (ocput (ocpush f oc) (f &p t))
                       (f &p (ocput oc t));
Induction min oc;
  intros; Refine Eq_refl;
  intros ___ l r lhyp t; Wave > lhyp; Refine Eq_refl;
  intros ___ l r rhyp t; Wave > rhyp; Refine Eq_refl;
Save;

Goal ocpush_here_lemma : {m,n|nat}{f:(fin n)->ml m}{oc:ml_occur n}
                         (Eq (ocpush f oc) (here m))->Eq oc (here n);
Cases min oc;
  intros; Refine Eq_refl;
Save;

Goal push_cases : {m,n|nat}{f:(fin n)->ml m}{t:ml n}
                  {Phi:(ml m)->Type}
                  {phi_oc:{u:ml m}
                          ({oc:ml_occur n}{i:fin n}
                           (Eq (ocput oc (V i)) t)->
                           Eq (ocput (ocpush f oc) (f i)) u)->
                          Phi u}
                  Phi (f &p t);
Induction min t;
  intros ___ i __;
    Refine phi_oc;
      Induction oc;
        Refine Eq_refl;
  intros ___ s t shyp thyp __;
    Refine phi_oc;
      Induction oc;
        intros oc;
          Refine shyp ([x:ml m]({i:fin n}(Eq (ocput oc (V i)) (s - t))->
              Eq (ocput (ocpush f oc) (f i)) (x - (f &p t)))->{i:fin n}
              (Eq (ocput oc (V i)) s)->
              Eq (ocput (ocpush f oc) (f i) - (f &p t)) (x - (f &p t)));
            intros u hyp1 hyp2 i qs;
              Wave > hyp1 ? ? qs;
                Refine Eq_refl;
        intros oc;
          Refine thyp ([x:ml m]({i:fin n}(Eq (ocput oc (V i)) (s - t))->
              Eq (ocput (ocpush f oc) (f i)) ((f &p s) - x))->{i:fin n}
              (Eq (ocput oc (V i)) t)->
              Eq ((f &p s) - ocput (ocpush f oc) (f i)) ((f &p s) - x));
            intros u hyp1 hyp2 i qt;
              Wave > hyp1 ? ? qt;
                Refine Eq_refl;
Save;

Goal push_comp_lemma :{l,m,n|nat}{f:(fin m)->ml l}{g:(fin n)->ml m}{t:ml n}
                      Eq (((op&p f) &o g) &p t) (f &p g &p t);
Induction t;
  intros; Refine Eq_refl;
  intros n s t sh th l m f g; Wave > (sh,th); Refine Eq_refl;
Save;


Goal push_comp_trick : {n,m,l|nat}{f:(fin m)->ml n}{g:(fin l)->fin m}
                       {t:ml l}Eq ((f &o g) &p t) (f &p ((V|m) &o g) &p t);
Induction min t;
  intros; Refine Eq_refl;
  intros n m l f g s t sh th; Wave > (sh,th); Refine Eq_refl;
Save;

Goal push_ext_lemma : {n,m|nat}{f,g:(fin n)->ml m}
                      {ext:{i:fin n}Eq (f i) (g i)}
                      {t:ml n}Eq (f &p t) (g &p t);
intros n m f g ext;
  Induction t;
    Immed;
    intros s t sh th;
      Refine lin_2_tri_0_resp_1;
        Immed;
Save;

Goal V_push_lemma : {n|nat}{t:ml n}Eq ((V|n) &p t) t;
Induction t;
  intros; Refine Eq_refl;
  intros n s t sh th; 
    Refine lin_2_tri_0_resp_1;
      Immed;
Save;

Goal push_eq_V_cases : {m,n|nat}{f:(fin n)->ml m}{t:ml n}{i:fin m}
                       {Phi:(ml n)->Type}
                       {phi_v:{j:fin n}(Eq (f j) (V i))->Phi (V j)}
                       (Eq (f &p t) (V i))->Phi t;
Induction min t;
  intros _______; Immed;
Save;

Configure Infix &c right 4;
Goal OCCOMP : <op&c:{n|nat}{p,q:ml_occur n}ml_occur n>
              <e1:{n|nat}{q:ml_occur n}Eq ((here n) &c q) q>
              <e2:{n|nat}{l:ml_occur n}{r:ml n}{q:ml_occur n}
                  Eq ((l &l r) &c q) ((l &c q) &l r)>
              {n|nat}{l:ml n}{r:ml_occur n}{q:ml_occur n}
                  Eq ((l &r r) &c q) (l &r (r &c q));
Eduardo p Then Dale;
SaveReductions op&c;

(*************************************************************************)
(********                                                         ********)
(********        ML Occurrence is a Concrete Category             ********)
(********                                                         ********)
(*************************************************************************)

Goal MLOCCUR : {n:nat}ARROW;
intros n;
Refine make_ARROW;
  Refine unit;
  intros; Refine ml n;
  intros; Refine ml_occur n;
  Dnf; intros __; Refine ocput;
  Dnf; intros _; Refine here n;
  Dnf; intros ___; Refine op&c;
  Dnf; intros; Refine Eq_refl;
  Dnf; intros ___;
    Induction T;
      intros; Refine Eq_refl;
      intros l r hyp; Wave > hyp; intros; Refine Eq_refl;
      intros l r hyp; Wave > hyp; intros; Refine Eq_refl;
Save;

Goal occur_only_lemma : {n|nat}{t:ml n}{oc:ml_occur n}(Eq t (ocput oc t))->
                        Eq oc (here n);
Induction t;
  Cases oc;
    intros; Refine Eq_refl;
  Induction min oc;
    intros; Refine Eq_refl;
    intros n t s sh th oc och qs;
      Claim {oc2:ml_occur n}(Eq (oc2 &c ((here n) &l t)) (here n))->Absurd;
      Refine ?+1 oc;
        Refine sh;
          Wave > CompApp (MLOCCUR n)|void|void|void;
            Immed;
      Induction oc2;
    intros n s t sh th oc och qt;
      Claim {oc2:ml_occur n}(Eq (oc2 &c (s &r (here n))) (here n))->Absurd;
      Refine ?+1 oc;
        Refine th;
          Wave > CompApp (MLOCCUR n)|void|void|void;
            Immed;
      Induction oc2;
Save;

(*************************************************************************)
(********                                                         ********)
(********        Representations of Substitution                  ********)
(********                                                         ********)
(*************************************************************************)

(* Abstract *)
Configure Infix &s left 4;
Inductive [op&s : nat->nat->Type] Theorems
Constructors
  [iota : {n:nat}n &s n]
  [subst : {m,n|nat}{f:m &s n}{u:ml n}{k:fin (suc n)}m &s (suc n)];

Configure Infix &sc right 3;
Goal SCOMP : <op&sc:{n,m,l|nat}{f:n &s m}{g:m &s l}n &s l>
             <e1:{n,m|nat}{f:n &s m}
                 Eq (f &sc (iota m)) f>
             {l,m,n|nat}{f:n &s m}{g:m &s l}{u:ml l}{k:fin (suc l)}
                 Eq (f &sc (subst g u k)) (subst (f &sc g) u k);
Eduardo g Then Dale;
SaveReductions op&sc;

Configure Infix &K right 4;
Goal KNOCK : <op&K:{n|nat}{k,i:fin (suc n)}opt (fin n)>
             <e1:{n|nat}Eq ((f_zero n) &K (f_zero n)) (none (fin n))>
             <e2:{n|nat}{i:fin n}
                 Eq ((f_zero n) &K (f_suc i)) (some i)>
             <e3:{n|nat}{k:fin n}
                 Eq ((f_suc k) &K (f_zero n)) (some k)>
             {n|nat}{u:ml n}{k,i:fin n}
                 Eq ((f_suc k) &K (f_suc i))
                    (if (k &E i) (none (fin n)) (some i));
Eduardo k Then Eduardo i Then Dale;
SaveReductions op&K;

Goal knock_cases : {n|nat}{k,i:fin (suc n)}{Phi:(opt (fin n))->Type}
                   {phi_q:(Eq k i)->Phi (none (fin n))}
                   {phi_n0:(Eq k (f_zero n))->{j:fin n}(Eq i (f_suc j))->
                           Phi (some j)}
                   {phi_ns0:{l:fin n}(Eq k (f_suc l))->(Eq i (f_zero n))->
                           Phi (some l)}
                   {phi_nss:{l,j:fin n}(Eq k (f_suc l))->(Eq i (f_suc j))->
                            (Neq l j)->Phi (some j)}
                   Phi (k &K i);
Cases min k Then Cases min i;
  intros; Refine phi_q (Eq_refl ?);
  intros; Refine phi_n0 (Eq_refl ?) ? (Eq_refl ?);
  intros; Refine phi_ns0 ? (Eq_refl ?) (Eq_refl ?);
  intros n j l _____;
    Refine fineq_cases ? ? ([H:bool]Phi (if H (none (fin n)) (some j)));
      intros lqj; Refine phi_q;
        Refine Eq_resp; Immed;
      Refine phi_nss ? ? (Eq_refl ?) (Eq_refl ?);
Save;

Goal knock_lemma : {n|nat}{k:fin (suc n)}Eq (k &K k) (none (fin n));
intros;
  Refine knock_cases ? ? ([H:opt (fin n)]Eq H (none (fin n)));
    intros; Refine Eq_refl;
    intros kq0; Qrepl kq0; KJunify;
    intros _ kqs; Qrepl kqs; KJunify;
    intros __ kqs; Qrepl kqs; KJunify; intros q nq; Refine nq q;
Save;

Goal HIT : <hit:{n|nat}{u:ml n}{k,i:fin (suc n)}ml n>
           {n|nat}{u:ml n}{k,i:fin (suc n)}
              Eq (hit u k i) (switch (V|n) u (k &K i));
Dale;
SaveReductions hit;

Goal SUBFN : <subfn:{m,n|nat}{f:m &s n}{i:fin n}ml m>
             <e1:{n|nat}Eq (subfn (iota n)) (V|n)>
             {m,n|nat}{f:m &s n}{u:ml n}{k:fin (suc n)}
                 Eq (subfn (subst f u k)) ((op&p (subfn f)) &o (hit u k));
Eduardo f Then Dale;
SaveReductions subfn;

Configure Infix &sa right 2;
Goal APPLY : <op&sa:{n,m|nat}{f:n &s m}{t:ml m}ml n>
             {n,m|nat}{f:n &s m}{t:ml m}Eq (op&sa f) (op&p (subfn f));
Dale;
SaveReductions op&sa;

(* Concrete *)
Record makeSubst [op<<:Type] Parameters [m,n:nat] Fields
  [Subst : (fin n)->ml m]
  [Lift : (fin m)->fin n]
  [Retract : {i:fin m}Eq (Subst (Lift i)) (V i)];
Discharge m ?;
Configure Memo op<< op<<;
Configure Memo op<< elim "op<<_elim";

Goal IOTA : {n:nat}n << n;
intros; Refine makeSubst;
  Refine V;
  Refine Id;
  intros; Refine Eq_refl;
Save;

Goal APPCONC : <op>>:{m,n|nat}{f:m << n}{t:ml n}ml m>
               {m,n|nat}{f:m << n}{t:ml n}Eq (f >> t) ((Subst f) &p t);
Dale;
SaveReductions op>>;

Goal op* : {n,m,l|nat}{f:n << m}{g:m << l}n << l;
Induction min f; Induction min g;
intros n m l fs fl fr gs gl gr;
Refine makeSubst;
  Refine (op&p fs) &o gs;
  Refine gl &o fl;
  intros i; Dnf;
    Wave > gr;
    Immed;
Save;

(* from Abstract to Concrete *)
Goal LIFT1 : <lift1:{n|nat}{k:fin (suc n)}{j:fin n}fin (suc n)>
             <e1:{n|nat}{j:fin n}Eq (lift1 (f_zero n) j) (f_suc j)>
             {n|nat}{k,j:fin n}
                 Eq (lift1 (f_suc k) j) (if (k &E j) (f_zero n) (f_suc j));
Eduardo k Then Dale;
SaveReductions lift1;

Goal lift1_cases : {n|nat}{k:fin (suc n)}{j:fin n}{Phi:(fin (suc n))->Type}
                   {phi:{i:fin (suc n)}(Neq k i)->
                        (Eq (k &K i) (some j))->Phi i}
                   Phi (lift1 k j);
Cases k;
  intros; Refine phi;
    Expand Neq; KJunify;
    Refine Eq_refl;
  intros n k' j __;
    Refine fineq_cases ? ? ([H:bool]Phi (if H (f_zero n) (f_suc j)));
      intros k'qj; Refine phi;
        Expand Neq; KJunify;
        Refine Eq_resp; Immed;
      intros k'nj; Refine phi;
        Expand Neq; KJunify; Immed;
        Wave > fineq_not_lemma ? ? k'nj;
        Refine Eq_refl;
Save;

Goal RETRACT1 : {n|nat}{u:ml n}{k:fin (suc n)}{j:fin n}
                Eq (hit u k (lift1 k j)) (V j);
Cases k;
  intros; Refine Eq_refl;
  intros;
    Refine fineq_cases ? ? ([H:bool]Eq (switch (V|n) u (f_suc x &K if H
    (f_zero n) (f_suc j))) (V j));
      intros; Refine Eq_resp; Immed;
      intros xnj;
        Wave > fineq_not_lemma ? ? xnj;
          Refine Eq_refl;
Save;

Goal LIFT : <lift:{m,n|nat}{f:m &s n}{j:fin m}fin n>
            <e1:{n|nat}{j:fin n}Eq (lift (iota n) j) j>
            {m,n|nat}{f:m &s n}{u:ml n}{k:fin (suc n)}{j:fin m}
                Eq (lift (subst f u k) j) (lift1 k (lift f j));
Eduardo f Then Dale;
SaveReductions lift;

Goal RETRACT : {m,n|nat}{f:m &s n}{j:fin m}Eq (subfn f (lift f j)) (V j);
Induction f;
  intros; Refine Eq_refl;
  intros;
    Wave > RETRACT1;
      Immed;
Save;

Goal AbsCon : {m,n|nat}{f:m &s n}m << n;
intros m n f;
Refine makeSubst;
  Refine subfn f;
  Refine lift f;
  Refine RETRACT f;
Save AbsCon;

Goal hit_lemma : {n|nat}{k:fin (suc n)}{t:ml (suc n)}{w:ml n}
                   {wnoc:{u:ml n}Eq (hit u k &p t) w}
                   Eq (((V|(suc n)) &o (lift1 k)) &p w) t;
Induction min t;
  intros n k i;
    Refine knock_cases ? ? ([H:opt (fin n)]{w:ml n}
        ({u:ml n}Eq (switch (V|n) u H) w)->
        Eq ((V|(suc n) &o lift1 k) &p w) (V i));
      intros _ w bad; Refine cut (bad (w - w)); KJunify;
      intros kq j iq w qw; Qrepl kq; Qrepl iq; Qrepl Eq_sym (qw w);
        Refine Eq_refl;
      intros l kq iq w qw; Qrepl kq; Qrepl iq; Qrepl Eq_sym (qw w);
        Wave > fineq_lemma; Refine Eq_refl;
      intros l j kq iq lnj w qw; Qrepl kq; Qrepl iq; Qrepl Eq_sym (qw w);
        Wave > fineq_not_lemma ? ? lnj; Refine Eq_refl;
  Cases w;
    intros n k x s t sh th qw; Refine cut (qw (V k)); KJunify;
    intros n s t k s' t' sh th qw;
      Claim {u:ml n}Eq (hit u k &p s') s;
      Claim {u:ml n}Eq (hit u k &p t') t;
        Wave > (sh ? ?+1,th ? ?+2); Refine Eq_refl;
      intros u; Refine cut (qw u); KJunify; intros; Immed;
      intros u; Refine cut (qw u); KJunify; intros; Immed;
Save;

(****************
Goal push_lemma : {n,m|nat}{f:n &s m}{s,t:ml m}
                  Eq (f &sa (s - t)) ((f &sa s) - (f &sa t));
Cases f Then intros Then Refine Eq_refl;
Save;

Goal step_lemma : {n,m|nat}{f:n &s m}{u:ml m}{k:fin (suc m)}{t:ml (suc m)}
                  Eq (f &sa (hit u k) &p t)
                     ((subst f u k) &sa t);
Induction t;
  intros; Refine Eq_refl;
  intros m s t sh th n f u k;
    Wave > (sh,th);
      Refine Eq_refl;
Save;

Goal app_push_convert : {m,n|nat}{f:m &s n}{t:ml n}
                        Eq (f &sa t) (((op&sa f) &o (V|?)) &p t);
Induction t;
  intros; Refine Eq_refl;
  intros n s t sh th; Wave < (sh,th);
    intros; Refine Eq_refl;
Save;
********************)
(*************************************************************************)
(********                                                         ********)
(********        Concrete Substitutions Concrete Category         ********)
(********                                                         ********)
(*************************************************************************)

Goal MLCONCSUBST : ARROW;
Refine make_ARROW;
  Refine nat;
  Refine ml;
  Refine op<<;
  Refine op>>;
  Refine IOTA;
  Refine op*;
  Dnf; Induction t;
    intros; Refine Eq_refl;
    intros n s t sh th; Wave > (sh,th); Refine Eq_refl;
  Induction T; Induction S;
    intros; Wave > push_comp_lemma; Refine Eq_refl;
Save;

Goal DeletionMGU : {n|nat}{t:ml n}
                   Maximal ? (UNIFIER MLCONCSUBST t t) (IOTA n);
intros; Refine make_Maximal;
  Refine Eq_refl;
  intros; Immed;
  intros; Wave > Right_Id MLCONCSUBST;
    Refine Eq_refl;
Save;

(*************************************************************************)
(********                                                         ********)
(********        ML Occur Check Things                            ********)
(********                                                         ********)
(*************************************************************************)

Goal CHECK : <check:{n|nat}{k:fin (suc n)}{t:ml (suc n)}opt (ml n)>
             <e1:{n|nat}{k,i:fin (suc n)}
                 Eq (check k (V i)) (switch ((some|(ml n)) &o (V|n)) 
                                            (none (ml n)) (k &K i))>
             {n|nat}{k:fin (suc n)}{s,t:ml (suc n)}
                 Eq (check k (s - t)) (try2 (op-|?) (check k s) (check k t));
Eduardo t Then Dale;
SaveReductions check;

Goal OCCHECK : <occheck : {n|nat}{k:fin (suc n)}{oc:ml_occur (suc n)}
                          opt (ml_occur n)>
               <e1:{n|nat}{k:fin (suc n)}
                   Eq (occheck k (here (suc n))) (some (here n))>
               <e2:{n|nat}{k:fin (suc n)}{l:ml_occur (suc n)}{r:ml (suc n)}
                   Eq (occheck k (l &l r))
                      (try2 (op&l|?) (occheck k l) (check k r))>
               {n|nat}{k:fin (suc n)}{l:ml (suc n)}{r:ml_occur (suc n)}
                   Eq (occheck k (l &r r))
                      (try2 (op&r|?) (check k l) (occheck k r));
Eduardo oc Then Dale;
SaveReductions occheck;

Goal occheck_lemma : {n|nat}{k:fin (suc n)}{oc:ml_occur (suc n)}{t:ml (suc n)}
                     Eq (try2 (ocput|?) (occheck k oc) (check k t))
                        (check k (ocput oc t));
Induction oc;
  intros n k t;
    Refine try2_cases ? ? ? ([H:opt (ml n)]Eq H (check k t)) Then Try KJunify;
      intros _; Refine Eq_sym;
      Refine Eq_sym;
  intros n l r lhyp k t;
    Refine cut (lhyp k t);
      Refine try2_cases ? ? ? ([H:opt (ml n)](Eq H (check k (ocput l t)))->
         Eq (try2 (ocput|n) (try2 (op&l|n) (occheck k l) (check k r))
              (check k t)) (try2 (op-|n) (check k (ocput l t)) (check k r)));
        intros l' t' ql' qt' qclt;
          Wave > (ql',qt'); Wave < qclt;
            Invert (check k r);
              intros r' qr'; Wave < qr'; Refine Eq_refl;
              intros qcr; Wave < qcr; Refine Eq_refl;
        intros qcl qclt; Wave > qcl; Wave < qclt; Refine Eq_refl;
        intros qct qclt; Wave > qct; Wave < qclt;
          Wave > try2_lemma; Refine Eq_refl;
  intros n l r rhyp k t;
    Refine cut (rhyp k t);
      Refine try2_cases ? ? ? ([H:opt (ml n)](Eq H (check k (ocput r t)))->
         Eq (try2 (ocput|n) (try2 (op&r|n) (check k l) (occheck k r))
              (check k t)) (try2 (op-|n) (check k l) (check k (ocput r t))));
        intros r' t' qr' qt' qcrt;
          Wave > (qr',qt'); Wave < qcrt;
            Invert (check k l);
              intros l' ql'; Wave < ql'; Refine Eq_refl;
              intros qcl; Wave < qcl; Refine Eq_refl;
        intros qcr qcrt; Wave > qcr; Wave < qcrt;
          Wave > try2_lemma; Refine Eq_refl;
        intros qcr qcrt; Wave > qcr; Wave < qcrt;
          Wave > try2_lemma; Refine Eq_refl;
Save;

Goal check_cases : {n|nat}{k:fin (suc n)}{t:ml (suc n)}
                   {Phi : (opt (ml n))->Type}
                   {phi_oc : {oc:ml_occur (suc n)}
                             (Eq t (ocput oc (V k)))->
                             Phi (none (ml n))}
                   {phi_no : {w:ml n}
                             ({u:ml n}Eq ((hit u k) &p t) w)->
                             Phi (some w)}
                   Phi (check k t);
Induction min t;
  intros n k i ___;
    Refine knock_cases ? ? ([H:opt (fin n)]Phi
    (switch (some|(ml n) &o V|n) (none (ml n)) H));
      intros kqi; Refine phi_oc (here (suc n)); Qrepl kqi; Refine Eq_refl;
      intros qk j qi; Refine phi_no; intros u; Qrepl qk; Qrepl qi;
        Refine Eq_refl;
      intros l qk qi; Refine phi_no; intros u; Qrepl qk; Qrepl qi;
        Refine Eq_refl;
      intros l j qk qi lnj; Refine phi_no; intros u; Qrepl qk; Qrepl qi;
        Wave > fineq_not_lemma ? ? lnj; Refine Eq_refl;
  intros n k s t sh th ___;
    Refine sh ([H:opt (ml n)]Phi (try2 (op-|n) H (check k t)));
      intros oc qoc; Refine phi_oc;
        Refine (oc &l t);
        Qrepl qoc;
          Refine Eq_refl;
      intros s' snoc;
        Refine th ([H:opt (ml n)]Phi (try2 (op-|n) (some s') H));
          intros oc qoc; Refine phi_oc;
            Refine (s &r oc);
            Qrepl qoc;
              Refine Eq_refl;
        intros t' tnoc;
          Refine phi_no;
            Wave > (snoc,tnoc);
              intros; Refine Eq_refl;
Save;

Goal max_elimination_lemma :
     {n|nat}{k:fin (suc n)}{t:ml (suc n)}{u:ml n}{chk:Eq (check k t) (some u)}
     Maximal ? (UNIFIER MLCONCSUBST (V k) t) (AbsCon (subst (iota n) u k));
intros n k t;
  Refine check_cases ? ? ([H:opt (ml n)]{u:ml n}{chk:Eq H (some u)}
  Maximal ? (UNIFIER MLCONCSUBST (V k) t) (AbsCon (subst (iota n) u k)))
  Then Try KJunify;
    intros w wnoc;
      Refine make_Maximal;
        Normal;
          Wave > knock_lemma;
          Wave > push_comp_lemma;
          Wave > wnoc;
            Refine Eq_refl;
        Expand Index Arrow;
          Induction g; Expand App Comp Obj;
          Equiv {l|nat}{Subst1:(fin (suc n))->ml l}{Lift1:(fin l)->fin (suc n)}
                {Retract1:{i:fin l}Eq (Subst1 (Lift1 i)) (V i)}
                (Eq (Subst1 k) (Subst1 &p t))->
                <h:l << n>{t:ml (suc n)}
                Eq (Subst (makeSubst Subst1 Lift1 Retract1) &p t)
                (Subst (h * AbsCon (subst (iota n) w k)) &p t);
            intros l gs gl gr gukt;
              Intros#; Refine makeSubst;
                Refine gs &o (lift1 k);
                Refine +2 push_ext_lemma;
                Claim {i:fin l}<j:fin n>Eq (op&o gs (lift1 k) j) (V i);
                Refine [i:fin l](?+3 i).1;
                Refine [i:fin l](?+2 i).2;

                intros i; Expand Subst;
                  Refine knock_cases ? ? ([H:opt (fin n)]Eq (gs i)
                  ((gs &o lift1 k) &p V|n &p switch (V|n) w H));
                    intros kqi; Qrepl Eq_sym kqi;
                      Wave > V_push_lemma; Wave > push_comp_trick gs (lift1 k);
                      Wave > hit_lemma k t w wnoc; Immed;
                    intros kq j iq; Qrepl kq; Qrepl iq; Refine Eq_refl;
                    intros m kq iq; Qrepl kq; Qrepl iq;
                      Wave > fineq_lemma; Refine Eq_refl;
                    intros m j kq iq mnj; Qrepl kq; Qrepl iq;
                      Wave > fineq_not_lemma ? ? mnj; Refine Eq_refl;

                intros i;
                  Refine knock_cases k (gl i)
                         ([H:opt (fin n)]<j:fin n>Eq (gs (lift1 k j)) (V i));
                    intros kqgli;
                      Refine push_eq_V_cases gs t i
                             ([H:ml (suc n)](Eq H t)->
                             <j:fin n>Eq (gs (lift1 k j)) (V i));
                        Refine +2 Eq_refl;
                        intros j qi qj;
                          Refine knock_cases j k ([H:opt (fin n)]
                          <j:fin n>Eq (gs (lift1 k j)) (V i));
                            intros jqk;
                              Refine [h:(Eq (hit (w - w) k &p t) w)->
                                     <j:fin n>Eq (gs (lift1 k j)) (V i)]
                                     h (wnoc (w - w));
                                Qrepl Eq_sym qj; Qrepl jqk;
                                Qrepl knock_lemma k;
                                KJunify;
                            intros jq x kq; Intros#;
                              Refine x;
                              Qrepl kq; Wave > fineq_lemma;
                              Qrepl Eq_sym qi; Qrepl jq; Refine Eq_refl;
                            intros x jq kq; Intros#;
                              Refine x;
                              Qrepl kq; Qrepl Eq_sym qi; Qrepl jq;
                                Refine Eq_refl;
                            intros x y jq kq xny; Intros#;
                              Refine x;
                              Qrepl kq; Qrepl Eq_sym qi; Qrepl jq;
                                Wave > fineq_not_lemma ? ? (Neq_sym xny);
                                  Refine Eq_refl;
                        Wave < gukt; Wave > kqgli; Immed;
                    intros kq x gliq; Intros#;
                      Refine x;
                        Qrepl kq; Wave < (gr i); Qrepl gliq;
                          Refine Eq_refl;
                    intros x kq gliq; Intros#;
                      Refine x;
                        Qrepl kq; Wave < (gr i); Qrepl gliq;
                          Wave > fineq_lemma; Refine Eq_refl;
                    intros y x kq gliq ynx; Intros#;
                      Refine x;
                        Qrepl kq; Wave < (gr i); Qrepl gliq;
                          Wave > fineq_not_lemma ? ? ynx; Refine Eq_refl;
Save;

(*************************************************************************)
(********                                                         ********)
(********        Rumours (should probably start sooner)           ********)
(********                                                         ********)
(*************************************************************************)

Configure Infix &m right 5;

Record rumour [Rumour:Type]
Fields
  [About:Type]
  [Intention:About->Type];
Configure Memo Rumour Rumour;
Configure Memo Rumour elim Rumour_elim;

Record substance [Substance:Type] Parameters [R:Rumour]
Fields
  [Subject:About R]
  [Substantiation:Intention R Subject];
Discharge R ?;
Configure Memo Substance Substance;
Configure Memo Substance elim Substance_elim;

Record Fr [from:Type] Parameters [n:nat] Fields
  [ArrowTo|nat]
  [TheArrow:ArrowTo &s n];
Configure Memo from from;
Configure Memo from elim from_elim;
Require from no confusion;
Require from eduardo;
Discharge n ?;

Goal MGU : Rumour;
Refine rumour;
  Refine {n|nat}{s,t:ml n}opt (from n);
  intros op&m;
    Refine {n|nat}{s,t:ml n}
           {Phi:(opt (from n))->Type}
           {phi_y:{m|nat}{u:m &s n}
                  (Maximal ? (UNIFIER MLCONCSUBST s t) (AbsCon u))->
                  Phi (some (Fr u))}
           {phi_n:({m|nat}{u:m << n}
                  (Why (UNIFIER MLCONCSUBST s t) u)->Absurd)->
                  Phi (none (from n))}
           Phi (s &m t);
Save;

Goal BOUNDED_MGU : Rumour;
Refine rumour;
  Refine {n|nat}{s,t:ml n}{F:opt (from n)}opt (from n);
  intros bmgu;
    Refine {n|nat}{s,t:ml n}{F:opt (from n)}
           {Phi:(opt (from n))->Type}
           {phi_y:{l,m|nat}{u:l &s m}{f:m &s n}
                  (Eq F (some (Fr f)))->
                  (Maximal ? (UNIFIER MLCONCSUBST (f &sa s) (f &sa t))
                             (AbsCon u))->
                   Phi (some (Fr (u &sc f)))}
           {phi_n:({l,m|nat}{u:l << m}{f:m &s n}
                   (Eq F (some (Fr f)))->
                   (Why (UNIFIER MLCONCSUBST (f &sa s) (f &sa t)) 
                        u)->Absurd)->
                  Phi (none (from n))}
           {phi_z:(Eq F (none (from n)))->Phi (none (from n))}
           Phi (bmgu s t F);
Save;

Goal bounded_enough : (Substance BOUNDED_MGU)->Substance MGU;
Induction 1; Expand Intention;
  intros bmgu bmgu_cases;
  Refine substance;
    Intros n s t;
      Refine bmgu s t (some (Fr (iota n)));
    Intros n s t ___; Dnf;
      Refine bmgu_cases Then Try KJunify;
        Qrepl V_push_lemma s; Qrepl V_push_lemma t; Immed;
        intros noUnif;
          Refine phi_n;
            intros m u must;
              Refine noUnif u (iota n) (Eq_refl ?);
                Wave > V_push_lemma; Immed;
Save;

Goal VARVAR : Rumour;
Refine rumour;
  Refine {n|nat}{i,j:fin n}opt (from n);
  intros VVU;
    Refine {n|nat}{i,j:fin n}{Phi:(opt (from n))->Type}
           {phi_y:{m|nat}{u:m &s n}
                  (Maximal ? (UNIFIER MLCONCSUBST (V i) (V j)) (AbsCon u))->
                  Phi (some (Fr u))}
           {phi_n:({m|nat}{u:m << n}
                  (Why (UNIFIER MLCONCSUBST (V i) (V j)) u)->Absurd)->
                  Phi (none (from n))}
           Phi (VVU i j);
Save;

Goal VARARR : Rumour;
Refine rumour;
  Refine {n|nat}{i:fin n}{s,t:ml n}opt (from n);
  intros VAU;
    Refine {n|nat}{i:fin n}{s,t:ml n}{Phi:(opt (from n))->Type}
           {phi_y:{m|nat}{u:m &s n}
                  (Maximal ? (UNIFIER MLCONCSUBST (V i) (s - t))
                   (AbsCon u))->
                  Phi (some (Fr u))}
           {phi_n:({m|nat}{u:m << n}
                  (Why (UNIFIER MLCONCSUBST (V i) (s - t)) u)->Absurd)->
                  Phi (none (from n))}
           Phi (VAU i s t);
Save;

Goal KNOCKV : <knockv:{n|nat}{i:fin (suc n)}{k:opt (ml n)}opt (from (suc n))>
              <e1:{n|nat}{i:fin (suc n)}
                  Eq (knockv i (none (ml n))) (some (Fr (iota (suc n))))>
              {n|nat}{i:fin (suc n)}{k:ml n}
                  Eq (knockv i (some k)) (some (Fr (subst (iota n) k i)));
Eduardo k Then Dale;
SaveReductions knockv;

Goal VVU : <vvu:{n|nat}{i,j:fin n}opt (from n)>
           {n|nat}{i,j:fin (suc n)}
           Eq (vvu i j) (knockv i (check i (V j)));
Eduardo n;
  Dale;
  Cases 2;
SaveReductions vvu;

Goal VVUS : Substance VARVAR;
Refine substance;
  Refine vvu;
  Expand Intention;
    Cases n; Cases i; (* silly zero case gone *)
    intros n i j _;
      Refine check_cases i (V j)
      ([H:opt (ml n)]
        ({m|nat}{u:m &s suc n}
         (Maximal MLCONCSUBST (UNIFIER MLCONCSUBST (V i) (V j)) (AbsCon u))->
         Phi (some (Fr u)))->
        (({m|nat}{u:m << suc n}(Why (UNIFIER MLCONCSUBST (V i) (V j)) u)->
          Absurd)->Phi (none (from (suc n))))->
      Phi (knockv i H)) ? ?;
        Cases oc;
          intros jqi; Qrepl jqi;
            intros phi_y phi_n; Refine phi_y;
              Refine make_Maximal;
                Refine Eq_refl;
                intros l g gu; Intros#;
                  Refine g;
                  intros t;
                    Wave > CompApp MLCONCSUBST; Wave > V_push_lemma;
                      Refine Eq_refl;
        intros w wnoc phi_y phi_n;
          Refine phi_y;
            Refine max_elimination_lemma;
              Refine switch_cases (V|n) (w - w) (i &K j)
                     ([H:ml n](Eq H w)->
                     Eq (switch (some|(ml n) &o V|n) (none (ml n)) (i &K j))
                        (some w));
                Refine +2 wnoc;
                intros s qs qw; Qrepl qs; Refine Eq_resp; Immed;
                KJunify;
Save;

Goal KNOCKA : <knocka:{n|nat}{i:fin (suc n)}{k:opt (ml n)}opt (from (suc n))>
              <e1:{n|nat}{i:fin (suc n)}
                  Eq (knocka i (none (ml n))) (none (from (suc n)))>
              {n|nat}{i:fin (suc n)}{k:ml n}
                  Eq (knocka i (some k)) (some (Fr (subst (iota n) k i)));
Eduardo k Then Dale;
SaveReductions knocka;

Goal VAU : <vau:{n|nat}{i:fin n}{s,t:ml n}opt (from n)>
           {n|nat}{i:fin (suc n)}{s,t:ml (suc n)}
           Eq (vau i s t) (knocka i (check i (s - t)));
Eduardo n;
  Dale;
  Cases 2;
SaveReductions vau;

Goal VAUS : Substance VARARR;
Refine substance;
  Refine vau;
  Expand Intention;
    Cases n; Cases i; (* gets the daft zero case *)
      intros n i s t _;
        Refine check_cases i (s - t) ([H:opt (ml n)](Eq (check i (s - t)) H)->
        ({m|nat}{u:m &s suc n}
         (Maximal MLCONCSUBST (UNIFIER MLCONCSUBST (V i) (s - t)) (AbsCon u)
          )->Phi (some (Fr u)))->
        (({m|nat}{u:m << suc n}(Why (UNIFIER MLCONCSUBST (V i) (s - t)) u)->
          Absurd)->Phi (none (from (suc n))))->
        Phi (knocka i H)) ? ?;
          Refine +2 Eq_refl;
          intros oc stqocpi chk phi_y phi_n; Refine phi_n;
            Equiv {m|nat}{u:m << suc n}{uist:Eq (u >> (V i)) (u >> (s - t))}
                  Absurd;
            intros;
              Refine [h:(Eq (u >> (s - t)) (u >> (ocput oc (V i))))->Absurd]
                     h (Eq_resp (op>> u) stqocpi);
                Equiv (Eq (u >> (s - t)) (u >> (ocput oc (V i))))->Absurd;
                Qrepl Eq_sym uist;
                  Qrepl Eq_sym (ocpush_lemma (Subst u) oc (V i));
                    intros cycle;
                      Refine [h:(Eq (s - t) (ocput oc (V i)))->Absurd]
                             h stqocpi;
                        Qrepl ocpush_here_lemma (Subst u) oc
                                (occur_only_lemma ? ? cycle);
                          KJunify;
          intros w wnoc chk phi_y phi_n; Refine phi_y;
            Refine max_elimination_lemma;
              Immed;
Save;

Goal BMGU :
    <bmgu:{n|nat}{s,t:ml n}{F:opt (from n)}opt (from n)>
    <e0:{n|nat}{s,t:ml (suc n)}
        Eq (bmgu s t (none (from (suc n)))) (none (from (suc n)))>
    <e1:{n|nat}{i,j:fin (suc n)}
        Eq (bmgu (V i) (V j) (some (Fr (iota (suc n))))) (Subject VVUS i j)>
    <e2:{n|nat}{i:fin (suc n)}{s,t:ml (suc n)}
        Eq (bmgu (V i) (s - t) (some (Fr (iota (suc n)))))
           (Subject VAUS i s t)>
    <e3:{n|nat}{s,t:ml (suc n)}{j:fin (suc n)}
        Eq (bmgu (s - t) (V j) (some (Fr (iota (suc n)))))
           (Subject VAUS j s t)>
    <e4:{n|nat}{s1,t1,s2,t2:ml (suc n)}
        Eq (bmgu (s1 - t1) (s2 - t2) (some (Fr (iota (suc n)))))
        (bmgu t1 t2 (bmgu s1 s2 (some (Fr (iota (suc n))))))>
    {n,m|nat}{s,t:ml (suc n)}{f:m &s n}{u:ml n}{k:fin (suc n)}
        Eq (bmgu s t (some (Fr (subst f u k))))
           (glue (bmgu ((hit u k) &p s) ((hit u k) &p t) (some (Fr f))) u k);
Eduardo n;
  Next +1;
  intros; Refine ml_zero_empty s;
  Eduardo s Then Eduardo t Then Eduardo F Then Try Dale;
    (* Vi Vj *)
    Eduardo 6;
      Eduardo TheArrow1 Then Dale;
    (* Vi s-t *)
    Eduardo 5;
      Eduardo TheArrow1 Then Dale;
    (* s-t Vj *)
    Eduardo 5;
      Eduardo TheArrow1 Then Dale;
    (* s1-t1 s2-t2 *)
    Eduardo 4;
      Eduardo TheArrow1 Then Dale;
Save; (* several years later *)

Goal GLUE : <glue:{n|nat}{F:opt (from n)}{u:ml n}{k:fin (suc n)}
                  opt (from (suc n))>
            <e1:{n|nat}{u:ml n}{k:fin (suc n)}
                Eq (glue (none (from n)) u k) (none (from (suc n)))>
            {m,n|nat}{f:m &s n}{u:ml n}{k:fin (suc n)}
                Eq (glue (some (Fr f)) u k) (some (Fr (subst f u k)));
Eduardo F
  Dale;
  Eduardo 1;
    Dale;
SaveReductions glue;

(***************************
[BMGU :
    <bmgu:{n|nat}{s,t:ml n}{F:opt (from n)}opt (from n)>
    <e0:{n|nat}{s,t:ml (suc n)}
        Eq (bmgu s t (none (from (suc n)))) (none (from (suc n)))>
    <e1:{n|nat}{i,j:fin (suc n)}
        Eq (bmgu (V i) (V j) (some (Fr (iota (suc n))))) (Subject VVUS i j)>
    <e2:{n|nat}{i:fin (suc n)}{s,t:ml (suc n)}
        Eq (bmgu (V i) (s - t) (some (Fr (iota (suc n)))))
           (Subject VAUS i s t)>
    <e3:{n|nat}{s,t:ml (suc n)}{j:fin (suc n)}
        Eq (bmgu (s - t) (V j) (some (Fr (iota (suc n)))))
           (Subject VAUS j s t)>
    <e4:{n|nat}{s1,t1,s2,t2:ml (suc n)}
        Eq (bmgu (s1 - t1) (s2 - t2) (some (Fr (iota (suc n)))))
        (bmgu t1 t2 (bmgu s1 s2 (some (Fr (iota (suc n))))))>
    {n,m|nat}{s,t:ml (suc n)}{f:m &s n}{u:ml n}{k:fin (suc n)}
        Eq (bmgu s t (some (Fr (subst f u k))))
           (glue (bmgu ((hit u k) &p s) ((hit u k) &p t) (some (Fr f))) u k)];
*********************)

Goal arrow_lemma : {n|nat}{s1,t1,s2,t2:ml n}
                   EQUIV (AND (UNIFIER MLCONCSUBST s1 s2)
                              (UNIFIER MLCONCSUBST t1 t2))
                         (UNIFIER MLCONCSUBST (s1-t1) (s2-t2));
intros _____; Refine UNIFIER_INJ2|MLCONCSUBST op- ?;
  Expand Inj2;
    KJunify; intros ___; Intros# Then Refine Eq_refl;
  intros; Refine Eq_refl;
Save;

Goal base_cases_enough : Substance BOUNDED_MGU;
Refine substance;
  Refine BMGU.1;
  Expand Intention;
  Cases min F;
    Induction min x1;
    Induction mid n;
      intros; Refine ml_zero_empty s;
      Induction mid s Then Cases mid t
              Then Induction mid TheArrow1 Then Wave 1 > BMGU.2;
        (* Vi Vj iota *)
        intros n hyp i j ____;
          Refine Substantiation VVUS;
            intros m u; Refine phi_y u (iota (suc n)) (Eq_refl ?);
            intros noUnif; Refine phi_n; KJunify; Immed;
        (* Vi Vj subst *)
        intros n m f w k nhyp fhyp i j  ____;
          Refine fhyp ? ? f ([H:opt (from n)]Phi (glue H w k))
          Then Try KJunify;
            intros l un max; Refine phi_y ? ? (Eq_refl ?); Immed;
            intros noUnif; Refine phi_n; KJunify; intros __;
              Refine noUnif ? ? (Eq_refl ?);
        (* Vi s-t iota *)
        intros n hyp i s t ____;
          Refine Substantiation VAUS;
            intros m u;
              Qrepl Eq_sym (V_push_lemma (V i));
              Qrepl Eq_sym (V_push_lemma (s - t));
                Refine phi_y ? ? (Eq_refl ?);
            intros noUnif; Refine phi_n; KJunify;
              Qrepl V_push_lemma (V i);
              Qrepl V_push_lemma (s - t);
                Immed;
        (* Vi s-t subst *)
        intros n m f w k nhyp fhyp i s t ____;
          Refine fhyp ? ? f ([H:opt (from n)]Phi (glue H w k))
          Then Try KJunify;
            intros l u max; Refine phi_y ? ? (Eq_refl ?);
              Wave > push_comp_lemma; Immed;
            intros noUnif; Refine phi_n; KJunify; intros ? ? bogus;
              Refine noUnif un ? (Eq_refl ?);
                Wave 3 < push_comp_lemma; Wave 1 > push_comp_lemma; Immed;
        (* s-t Vj iota *)
        intros n nhyp s t shyp thyp j ____;
          Refine Substantiation VAUS;
            intros m u max; Refine phi_y ? ? (Eq_refl ?);
              Refine EquivMax; Refine +2 max;
                Qrepl V_push_lemma s; Qrepl V_push_lemma t;
                  Refine UNIFIER_SYM;
            intros noUnif; Refine phi_n; KJunify;
              Qrepl V_push_lemma s; Qrepl V_push_lemma t;
                intros l u bogus; Refine noUnif u;
                  Refine (UNIFIER_SYM ? ? ? ?).1 bogus;
        (* s-t Vj subst *)
        intros n m f w k nhyp fhyp s t shyp thyp j ____;
          Refine fhyp ? ? f ([H:opt (from n)]Phi (glue H w k))
          Then Try KJunify;
            intros l u max; Refine phi_y ? ? (Eq_refl ?);
              Wave > push_comp_lemma; Immed;
            intros noUnif; Refine phi_n; KJunify; intros __ bogus;
              Refine noUnif u ? (Eq_refl ?);
                Wave 2 < push_comp_lemma; Immed;
        (* s1-t1 s2-t2 iota *)
        intros n nhyp s1 t1 s1h t1h s2 t2 ____;
          Refine s1h s2 ? ([H:opt (from (suc n))]Phi (BMGU.1 t1 t2 H))
                 Then Try KJunify;
            intros ls us maxs;
              Refine t1h Then Try KJunify;
                intros lt ut maxt;
                  Refine phi_y ? ? (Eq_refl ?);
                    Refine EquivMax;
                      Refine +1 arrow_lemma;

(* should be the Max_ext_lemma *)
Claim {m,n|nat}{P:Closed MLCONCSUBST n}{f,g:m << n}
      ({t:ml n}Eq (f >> t) (g >> t))->(Maximal ? P f)->Maximal ? P g;

                      Refine ?+1 ? ((AbsCon ut) * (AbsCon us));

(* should be the AbsCon_comp_lemma *)
Claim {l,m,n|nat}{f:n &s m}{g:m &s l}{t:ml l}
      Eq ((AbsCon (f &sc g)) >> t) (((AbsCon f) * (AbsCon g)) >> t);

                        Wave > ?+3; intros; Refine Eq_refl;

                        Refine Greedy;
                          Refine maxs;
                          Refine MaxBoundUnifier;
                            Wave > V_push_lemma; Refine maxt;

(* proof of Max_ext_lemma *)
intros a b P g h X maxg; Refine make_Maximal;
  Refine Ext P; Refine +1 X; Refine Holds maxg;
  intros c d Pd; Intros#;
    Refine (Factor maxg Pd).1;
      intros y;
        Wave > CompApp MLCONCSUBST; Wave < X; Wave 1 < CompApp MLCONCSUBST;
        Refine (Factor maxg Pd).2 y;

(* proof of AbsCon_comp_lemma *)
Induction g;
  Wave > CompApp MLCONCSUBST; Wave > V_push_lemma; intros; Refine Eq_refl;
  intros a b c d e hyp y;
    Wave > CompApp MLCONCSUBST; Wave > push_comp_lemma;
    Wave > hyp; Wave > CompApp MLCONCSUBST;
      intros; Refine Eq_refl;

            intros noUnif;
              Refine phi_n; KJunify;
                Qrepl V_push_lemma s1; Qrepl V_push_lemma t1;
                Qrepl V_push_lemma s2; Qrepl V_push_lemma t2;
                  intros __ bogus;
                    Refine noUnif ? ? (Eq_refl ?);
                      Refine +1 (Factor maxs ?).1;
                        Next +2; Wave > V_push_lemma;
                          Refine ((arrow_lemma s1 t1 s2 t2 u).2 bogus).1;
                            Equiv Eq
(((Factor maxs
              (([goal1:Eq (App MLCONCSUBST u s1) (App MLCONCSUBST u s2)]
                Eq_J_sym (V_push_lemma s1)
                 ([here|ml (suc n)][_:Eq here s1]
                  Eq (App MLCONCSUBST u here)
                   (App MLCONCSUBST u (V|(suc n) &p s2)))
                 (Eq_J_sym (V_push_lemma s2)
                   ([here|ml (suc n)][_:Eq here s2]
                    Eq (App MLCONCSUBST u s1) (App MLCONCSUBST u here)) goal1)
                ) ((((arrow_lemma s1 t1 s2 t2 u)).2 bogus)).1))).1 >>
                 (AbsCon us) >> t1)
(((Factor maxs
              (([goal1:Eq (App MLCONCSUBST u s1) (App MLCONCSUBST u s2)]
                Eq_J_sym (V_push_lemma s1)
                 ([here|ml (suc n)][_:Eq here s1]
                  Eq (App MLCONCSUBST u here)
                   (App MLCONCSUBST u (V|(suc n) &p s2)))
                 (Eq_J_sym (V_push_lemma s2)
                   ([here|ml (suc n)][_:Eq here s2]
                    Eq (App MLCONCSUBST u s1) (App MLCONCSUBST u here)) goal1)
                ) ((((arrow_lemma s1 t1 s2 t2 u)).2 bogus)).1))).1 >>
                 (AbsCon us) >> t2);
                             Wave 2 < CompApp MLCONCSUBST;
                      Wave 2 < (Factor maxs
                (Eq_J_sym (V_push_lemma s1)
                  ([here|ml (suc n)][_:Eq here s1]
                   Eq (App MLCONCSUBST u here)
                    (App MLCONCSUBST u (V|(suc n) &p s2)))
                  (Eq_J_sym (V_push_lemma s2)
                    ([here|ml (suc n)][_:Eq here s2]
                     Eq (App MLCONCSUBST u s1) (App MLCONCSUBST u here))
                    ((((arrow_lemma s1 t1 s2 t2 u)).2 bogus)).1))).2;
                          Refine ((arrow_lemma s1 t1 s2 t2 u).2 bogus).2;
            intros noUnif; Wave 1 > BMGU.2;
              Refine phi_n Then KJunify;
                Qrepl V_push_lemma s1; Qrepl V_push_lemma t1;
                Qrepl V_push_lemma s2; Qrepl V_push_lemma t2;
                intros __ bogus;
                  Refine noUnif u ? (Eq_refl ?);
                    Wave > V_push_lemma;
                      Refine ((arrow_lemma s1 t1 s2 t2 u).2 bogus).1;
        (* s1-t1 s2-t2 subst *)
        intros m n f w k nhyp fhyp s1 t1 s1h t1h s2 t2 ____;
          Refine fhyp ? ? f ([H:opt (from m)]Phi (glue H w k))
          Then Try KJunify;
           intros l u max; Refine phi_y ? ? (Eq_refl ?);
             Wave > push_comp_lemma; Immed;
           intros noUnif; Refine phi_n; KJunify; intros __ bogus;
             Refine noUnif u ? (Eq_refl ?);
               Wave < push_comp_lemma; Immed;
        (* stillborn *)
        Cases min n;
          intros; Refine ml_zero_empty s;
          intros n s t ____;
            Wave 1 > BMGU.2;
              Refine phi_z (Eq_refl ?);
Save;

Goal MGUS : Substance MGU;
Refine bounded_enough;
  Refine base_cases_enough;
    Refine BMGU;
Save;

[op&m = Subject MGUS];

(Normal (V (f_zero zero)) &m (V (f_zero zero)));

(Normal (V (f_zero zero)) &m ((V (f_zero zero)) - (V (f_zero zero))));

(Normal (V (f_zero (suc zero))) &m (V (f_suc (f_zero zero))));

(Normal ((V (f_zero two)) - (V (f_zero two))) &m
        ((V (f_suc (f_zero one))) - (V (f_suc (f_suc (f_zero zero))))));

(Normal ((V (f_zero two)) - (V (f_zero two))) &m
        (((V (f_suc (f_zero one))) - (V (f_suc (f_zero one)))) -
         (V (f_suc (f_suc (f_zero zero))))));

(Normal ((V (f_zero one)) - (V (f_suc (f_zero zero)))) &m
        ((((V (f_suc (f_zero zero))) - (V (f_suc (f_zero zero)))) -
         (V (f_zero one)))));