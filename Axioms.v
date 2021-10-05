Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.ChoiceFacts.

Require Import Notation.
Require Import GeneralTactics.

Require Export Coq.Logic.Classical.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.PropExtensionality.

(* We accept the following axioms:
   - excluded middle
   - functional extensionality
   - propositional extensionality
   - choice on propositional truncations

   From which, we derive:
   - proof irrelevance 
   - UIP and equivalents
   - prop degeneracy
   - functional choice
   - relational choice
 *)

(* classical tactics *)

Tactic Notation "destruct" "classic" uconstr(c) "as" ident(H) :=
  destruct (classic c) as [H|H].

Tactic Notation "destruct" "classic" uconstr(c) :=
  let x := fresh in
  destruct classic c as x.

Tactic Notation "contradict" "goal" hyp(H) :=
  apply NNPP; intro H.

Tactic Notation "contradict" "goal" :=
  let contra := fresh "contra" in
  apply NNPP; intro contra.


(* Consequences of classical LEM *)

Lemma proof_irrelevance : forall (P: Prop) (p1 p2: P),
  p1 = p2.
Proof using.
  intros *.
  apply proof_irrelevance_cci.
  exact classic.
Qed.

Lemma uip : forall A (x y: A) (p q: x = y),
  p = q.
Proof using.
  intros.
  apply proof_irrelevance.
Qed.

Lemma uip_refl : forall A (x: A) (p: x = x),
  p = eq_refl x.
Proof using.
  intros *.
  apply uip.
Qed.

Lemma K : forall A (x: A) (P: x = x -> Type),
  P (eq_refl x) ->
  forall p: x = x, P p.
Proof using.
  intros.
  now rewrite uip_refl.
Qed.

Lemma eq_rect_eq : forall A (x: A) (P: A -> Type) (y: P x) (h: x = x),
  y = eq_rect x P y x h.
Proof using.
  intros *.
  now rewrite (uip_refl _ _ h).
Qed.

Theorem inj_pairT2 :
  forall A (P: A -> Type) a (x y: P a),
    ⟨a, x⟩ = ⟨a, y⟩ ->
    x = y.
Proof using.
  intros.
  inversion_sigma.
  now find rewrite <- eq_rect_eq in.
Qed.

#[global]
Hint Resolve inj_pair2 inj_pairT2: eqdep.


(* Dependent inversion tactics leveraging LEM *)

Ltac destr_sigma_eq :=
  repeat match goal with 
  | H: existT _ _ _ = existT _ _ _ |- _ =>
      simple apply inj_pairT2 in H
  end.

Tactic Notation "dependent" "inv" hyp(H) :=
  inv H;
  destr_sigma_eq;
  subst!.

Tactic Notation "dependent" "inv" hyp(H) "as" simple_intropattern(pat) :=
  inv H as pat;
  destr_sigma_eq;
  subst!.

Tactic Notation "dependent" "invc" hyp(H) :=
  invc H;
  destr_sigma_eq;
  subst!.

Tactic Notation "dependent" "invc" hyp(H) "as" simple_intropattern(pat) :=
  invc H as pat;
  destr_sigma_eq;
  subst!.


(* Here we give a redefinition of the JMeq construct. Unfortunately, the 
   existing JMeq definition is irrevocably tied to the JMeq_eq axiom,
   which we'd rather not accept here, since it can be derived by 
   UIP (and by extesion, LEM).
 *)

(* heq stands for "heterogeneous equality" *)
Unset Elimination Schemes.
Inductive heq (A: Type) (x : A) : forall B : Type, B -> Prop :=
	| heq_refl : heq A x A x.
Set Elimination Schemes.
Arguments heq {A} x {B} y.
Arguments heq_refl {A} x.

Notation "x ~= y" := (heq x y) (at level 70, no associativity).

(* Note: this is in fact equivalent to UIP. *)
Lemma heq_eq : forall A (x y: A), 
  x ~= y ->
  x = y.
Proof using.
  intros * Heq.
  now dependent inv Heq.
Qed.

Theorem heq_rect : forall (A: Type) (x: A) (P : A -> Type),
  P x ->
  forall y : A, x ~= y -> P y.
Proof using.
  intros * ? * Heq.
  apply heq_eq in Heq.
  now induction Heq.
Qed.

Lemma heq_rec : forall (A: Type) (x: A) (P : A -> Set),
  P x ->
  forall y : A, x ~= y -> P y.
Proof (heq_rect).

Lemma heq_ind : forall (A: Type) (x: A) (P : A -> Prop),
  P x ->
  forall y : A, x ~= y -> P y.
Proof (heq_rect).


(* Extensionality *)

(* Modified from `Coq.Logic.FunctionalExtensionality` to include propositional
   extensionality
 *)
Tactic Notation "extensionality" :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (propositional_extensionality X Y) ||
     apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality)
  end.

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
    ((apply (propositional_extensionality X Y); split) ||
     apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality) ; intro x
  end.

(* Note, LEM and prop extensionality would also follow from assuming 
   degeneracy. Doing so would lessen our number of axioms. However, 
   having both LEM and prop extensionality axiomitzed individually is 
   a better separation of concerns.
 *)
Theorem prop_degeneracy : forall A: Prop, 
  A = True \/ A = False.
Proof using.
  apply prop_ext_em_degen.
  - exact propositional_extensionality.
  - exact classic.
Qed.

Lemma true_neq_false : True <> False.
Proof using.
  intro H.
  now induction H.
Qed.

Lemma provable_is_true : forall A: Prop,
  A = (A = True).
Proof using.
  intros *.
  extensionality H.
  - now (destruct (prop_degeneracy A); subst).
  - symmetry in H.
    now induction H.
Qed.

Lemma provable_contradiction_is_false : forall A: Prop,
  (~A) = (A = False).
Proof using.
  intros *.
  extensionality H.
  - now (destruct (prop_degeneracy A); subst).
  - intros ?.
    now induction H.
Qed.


(* convenient rewrite rules from LEM + prop extensionality *)

Theorem rew_NNPP: forall P: Prop,
  (~~P) = P.
Proof using.
  intros *.
  extensionality.
  split.
  - apply NNPP.
  - auto.
Qed.

Theorem rew_not_and : forall P Q: Prop,
  (~ (P /\ Q)) = ~P \/ ~Q.
Proof using.
  intros *.
  extensionality H.
  - now apply not_and_or.
  - now apply or_not_and.
Qed.

Theorem rew_not_or : forall P Q: Prop,
  (~ (P \/ Q)) = ~P /\ ~Q.
Proof using.
  intros *.
  extensionality H.
  - now apply not_or_and.
  - now apply and_not_or.
Qed.

Theorem rew_imply_or : forall P Q: Prop,
  (P -> Q) = ~P \/ Q.
Proof using.
  intros *.
  extensionality H.
  - now apply imply_to_or.
  - now apply or_to_imply.
Qed.

Theorem rew_not_all : forall U (P:U -> Prop),
  (~ forall n, P n) = exists n, ~ P n.
Proof using.
  intros *.
  extensionality H.
  - now apply not_all_ex_not.
  - now apply ex_not_not_all.
Qed.

Theorem rew_not_ex : forall U (P:U -> Prop),
  (~ exists n, P n) = forall n, ~ P n.
Proof using.
  intros *.
  extensionality H.
  - now apply not_ex_all_not.
  - now apply all_not_not_ex.
Qed.


(* Choice *)

Axiom choice : forall (A: Type) (B: A -> Type),
  (forall x, inhabited (B x)) ->
  inhabited (forall x, B x).

Lemma fun_choice : forall A B (R: A -> B -> Prop),
  (forall a, exists b, R a b) ->
  exists f: A -> B, forall a, R a (f a).
Proof using.
  intros * Rltotal.
  transform Rltotal (Π x, inhabited {y | R x y}).
  { intro a.
    specialize (Rltotal a).
    destruct exists Rltotal y.
    constructor.
    now exists y.
  }
  apply choice in Rltotal.
  destruct Rltotal as [Rltotal].
  define exists.
  - intro a.
    specialize (Rltotal a).
    now destruct Rltotal.
  - intros *.
    simpl.
    now destruct (Rltotal a).
Qed.

Theorem dependent_choice : forall {A: Type} {B: A -> Type} (R: forall a, B a -> Prop),
  (forall a, exists b, R a b) ->
  exists f: (forall a, B a),
    forall a, R a (f a).
Proof using.
  apply non_dep_dep_functional_choice.
  exact fun_choice.
Qed.

Lemma rel_choice : forall A B (R: A -> B -> Prop),
  (forall x, exists y, R x y) -> 
  exists R': A -> B -> Prop, 
    subrelation R' R /\
    forall x, exists! y, R' x y.
Proof using.
  intros * Rltotal.
  transform Rltotal (Π x, inhabited {y | R x y}).
  { intro a.
    specialize (Rltotal a).
    destruct exists Rltotal y.
    constructor.
    now exists y.
  }
  apply choice in Rltotal.
  destruct Rltotal as [Rltotal].
  define exists.
  - intro a.
    specialize (Rltotal a).
    destruct exists Rltotal b.
    exact (λ x, b = x).
  - simpl.
    split.
    + unfold subrelation.
      intros * ?.
      destruct (Rltotal x).
      now subst.
    + intros *.
      destruct (Rltotal x) as [y ?].
      now exists y.
Qed.
