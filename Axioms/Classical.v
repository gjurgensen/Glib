Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalFacts.

Require Import Notation.
Require Import GeneralTactics.

Require Export Coq.Logic.Classical.


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

