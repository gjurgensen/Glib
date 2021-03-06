Require Import TacticCombinators.

(* Overwrite exists tactic to support multiple instantiations 
   (up to four)
 *)
Tactic Notation "exists" uconstr(x1) :=
  exists x1.
Tactic Notation "exists" uconstr(x1) uconstr(x2) :=
  exists x1; exists x2.
Tactic Notation "exists" uconstr(x1) uconstr(x2) uconstr(x3) :=
  exists x1 x2; exists x3.
Tactic Notation "exists" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  exists x1 x2 x3; exists x4.


(* destruct variants *)

Tactic Notation "destruct" "multi" hyp(h1) hyp(h2) :=
  destruct h1; destruct h2.
Tactic Notation "destruct" "multi" hyp(h1) hyp(h2) hyp(h3) :=
  destruct multi h1 h2; destruct h3.
Tactic Notation "destruct" "multi" hyp(h1) hyp(h2) hyp(h3) hyp(h4) :=
  destruct multi h1 h2 h3; destruct h4.

Tactic Notation "destruct" "exists" hyp(H) ident(id) :=
  destruct H as [id H].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) :=
  destruct H as [id1 [id2 H]].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) ident(id3) :=
  destruct H as [id1 [id2 [id3 H]]].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) ident(id3) ident (id4) :=
  destruct H as [id1 [id2 [id3 [id4 H]]]].

Tactic Notation "destruct" "or" hyp(H) := destruct H as [H|H].

(* Clear variants. Tactics postfixed with "c" clear a hypothesis
   after using it.
 *)

Tactic Notation "applyc" hyp(H) := apply H; clear H.
Tactic Notation "applyc" hyp(H) "in" hyp(H2) := apply H in H2; clear H.
Tactic Notation "eapplyc" hyp(H) := eapply H; clear H.
Tactic Notation "eapplyc" hyp(H) "in" hyp(H2) := eapply H in H2; clear H.

Ltac specializec H x := specialize (H x); clear x.


(* Unfold one layer *)
Tactic Notation "expand" constr(x) := unfold x; fold x.
Tactic Notation "expand" constr(x) "in" hyp(H) := unfold x in H; fold x in H.
Tactic Notation "expand" constr(x) "in" "*" := unfold x in *; fold x in *.


(* Like `contradiction`, but introduces unification variables instead of failing *)
Tactic Notation "econtradiction" uconstr(u) := exfalso; eapply u.

(* `pose new proof`, variant of `pose proof` that fails if such a hypothesis
   already exists in the context. Useful for automation which saturates the 
   context with generated facts
 *)

Ltac fail_if_in_hyps H :=
  let t := type of H in
  lazymatch goal with 
  | [_: t |- _] => fail "This proposition is already assumed"
  | [_: _ |- _] => idtac
  end.

Tactic Notation "pose" "new" "proof" constr(H) :=
  fail_if_in_hyps H;
  pose proof H.

Tactic Notation "pose" "new" "proof" constr(H) "as" ident(H2) :=
  fail_if_in_hyps H;
  pose proof H as H2.


(* Maximally recursive split *)
Ltac _max_split := try (split; _max_split).
Tactic Notation "max" "split" := _max_split.


(* Copy a hypothesis *)
Tactic Notation "copy" hyp(H) :=
  let H' := fresh H in
  pose proof H as H'.

Tactic Notation "copy" hyp(H) ident(I) := pose proof H as I.


(* Overwrite a hypothesis *)
Ltac overwrite H c := 
  let temp := fresh in
  pose proof c as temp;
  clear H;
  rename temp into H.

Tactic Notation "transform" hyp(H) uconstr(c) :=
  let _temp := fresh in
  assert (_temp : c);
  [|overwrite H _temp; clear _temp].

Tactic Notation "transform" hyp(H) uconstr(c) "by" tactic(tac) :=
  let _temp := fresh in
  assert (_temp : c);
  [tac|overwrite H _temp; clear _temp].


(* When `unset x` is invoked with hypothesis `x := t` (commonly introduced by 
   tactic `set`), replaces all instances of `x` with `t`, and clears `x`.
 *)
Ltac unset x := unfold x in *; clear x.


(* A sylistic alias for `admit`. Used to distinguish admitted goals
   which you know how to solve and that you plan come back to once the 
   difficult proof goals are solved.
 *)
Ltac todo := admit.


(* `forward` conducts forward reasoning by eliminating the assumption 
   in an implication. Optionally, you can supply a tactic with the `by` clause.
   E.g.:
   with hypothesis `H: x = x -> foo`, one can invoke `forward H by reflexivity`. 
   The hypothesis is then replaced with `H: foo`.
 *)

Tactic Notation "forward" hyp(H):=
  match type of H with
  | ?x -> _ =>
      let H' := fresh in 
      assert (H': x); 
        [| specialize (H H'); clear H']
  end.

Tactic Notation "forward" hyp(H) "by" tactic(tac) :=
  forward H; [solve [tac]|].


(* "max" variant of `forward`. Invokes forward on each assumption of a chained implication *)

Ltac _max_forward H := try (forward H; [|_max_forward H]).
Tactic Notation "max" "forward" hyp(H) := _max_forward H.

Ltac _max_forward_by H tac := try (forward H by tac; [|_max_forward_by H tac]).
Tactic Notation "max" "forward" hyp(H) "by" tactic(tac) := _max_forward_by H tac.

(* Solve a (registered) reflexive relation by proving the arguments equal *)
Ltac reflexive := 
  match goal with 
  | |- _ ?x ?y =>
      replace x with y;
        [ reflexivity
        | try easy; symmetry
        ]
  end.


(* Taken from StructTact 
https://github.com/uwplse/StructTact/blob/a0f4aa3491edf27cf70ea5be3190b7efa8899971/theories/StructTactics.v#L309
 *)
Ltac break_let :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.


(* Specialize hypothesis with a unification variable *)
Ltac especialize H := 
  match type of H with 
  | forall x : ?T, _ => 
      let x' := fresh x in
      evar (x': T);
      specialize (H x');
      unfold x' in H;
      clear x'
  end.

(* Like especialize, but doesn't lose term definitions *)
Ltac especialize_term H :=
  match type of H with 
  | forall x : ?T, _ => 
      let x' := fresh x in
      evar (x': T);
      let _temp := fresh in 
      epose (_temp := H x');
      unfold x' in _temp; clear x';
      unfold H in _temp; clear H;
      rename _temp into H
  end.


(* More tactic-equivalents which don't lose term definitions *)

(* Like `assert`, but doesn't hide underlying term *)
Tactic Notation "define" uconstr(c) "as" ident(H) :=
  unshelve evar (H : c).

Tactic Notation "define" uconstr(c) "as" ident(H) "by" tactic(tac) :=
  define c as H; [solve[tac]|].

Tactic Notation "define" uconstr(c) :=
  let H := fresh in
  define c as H.

Tactic Notation "define" uconstr(c) "by" tactic(tac) :=
  define c; [solve[tac]|].

Ltac _define_exists_aux :=
  let def_ex_with := fun A => 
        let _temp := fresh in 
        define A as _temp; 
        [|exists _temp;
          unfold _temp;
          clear _temp]
  in match goal with 
  | |- @ex   ?A _ => def_ex_with A
  | |- @sig  ?A _ => def_ex_with A
  | |- @sigT ?A _ => def_ex_with A
  end.
Ltac _define_exists :=
  _define_exists_aux + (
    match goal with 
    | |- ?x _ _ _ _ _  => unfold x
    | |- ?x _ _ _ _    => unfold x
    | |- ?x _ _ _      => unfold x
    | |- ?x _ _        => unfold x
    | |- ?x _          => unfold x
    | |- context[?x _] => unfold x
    end;
    _define_exists
  ).
Tactic Notation "define" "exists" :=
  _define_exists.

Tactic Notation "define" "exists" "by" tactic(tac) :=
  define exists; [solve[tac]|].
  
Ltac specialize_term H x :=
  let _temp := fresh in 
  epose (_temp := H x);
  unfold H in _temp;
  clear H;
  rename _temp into H.

Tactic Notation "overwrite_term" hyp(H) uconstr(c) :=
  let _temp := fresh in
  epose (_temp := c);
  unfold H in _temp;
  clear H;
  rename _temp into H.

(* Note, this is vastly less powerful than `apply` *)
Tactic Notation "apply_term" uconstr(c) "in" hyp(H) :=
  let _temp := fresh in 
  epose (_temp := c);
  repeat (overwrite_term H (_temp H) + especialize_term _temp);
  unfold _temp in H;
  clear _temp.

(* This will replace the local definition with an equality *)
Tactic Notation "destruct_term" hyp(H)
  "as" simple_intropattern(pat) "eqn" ":" ident(i) :=
  let _temp := fresh in 
  rename H into _temp;
  destruct _temp as pat eqn:i;
  unfold _temp in i;
  clear _temp.

Tactic Notation "destruct_term" hyp(H) "eqn" ":" ident(i) :=
  let _temp := fresh in 
  rename H into _temp;
  destruct _temp eqn:i;
  unfold _temp in i;
  clear _temp.


(* repeat one or more times *)
Tactic Notation "repeat+" tactic(tac) :=
  tac; repeat tac.


(* `now` tactic with support for easy goals with existentials *)
Tactic Notation "enow" tactic(tac) :=
  (now tac) + (tac; solve [eassumption + eauto + now eexists]).


(* Find a hypothesis to apply the tactic to. Fails on non-progress. *)
Tactic Notation "find" tactic(tac) :=
  match goal with 
  | H : _ |- _ => progress tac H
  end.

Tactic Notation "find" "apply" :=
  find (fun H => apply H).
Tactic Notation "find" "applyc" :=
  find (fun H => applyc H).

Tactic Notation "find" "eapply" :=
  find (fun H => eapply H).
Tactic Notation "find" "eapplyc" :=
  find (fun H => eapplyc H).

Tactic Notation "find" "inversion" :=
  find (fun H => inversion H).

Tactic Notation "find" "rewrite" "->" :=
  find (fun H => rewrite -> H).
Tactic Notation "find" "rewrite" "->" uconstr(u) "in" :=
  find (fun H => rewrite -> u in H).

Tactic Notation "find" "rewrite" "<-" :=
  find (fun H => rewrite <- H).
Tactic Notation "find" "rewrite" "<-" uconstr(u) "in" :=
  find (fun H => rewrite <- u in H).

Tactic Notation "find" "rewrite" :=
  find rewrite -> + find rewrite <-.
Tactic Notation "find" "rewrite" uconstr(u) "in" :=
  find rewrite -> u in + find rewrite <- u in.

Tactic Notation "find" "specialize" uconstr(u1) :=
  find (fun H => specialize (H u1)).
Tactic Notation "find" "specialize" uconstr(u1) uconstr(u2) :=
  find (fun H => specialize (H u1 u2)).
Tactic Notation "find" "specialize" uconstr(u1) uconstr(u2) uconstr(u3) :=
  find (fun H => specialize (H u1 u2 u3)).
Tactic Notation "find" "specialize" uconstr(u1) uconstr(u2) uconstr(u3) uconstr(u4) :=
  find (fun H => specialize (H u1 u2 u3 u4)).

(* Like assumption, but instead of finding a hypothesis to solve by exact, it 
   finds one to solve by `apply`
 *)
Tactic Notation "assumption!" :=
  solve [find apply].


Tactic Notation "subst!" :=
  subst;
  repeat match goal with 
  | H : ?x = ?x |- _ => clear H
  end.


(* Improved inversion *)

Tactic Notation "inv" hyp(H) :=
  inversion H;
  subst!.

Tactic Notation "inv" hyp(H) "as" simple_intropattern(pat) :=
  inversion H as pat;
  subst!.

Tactic Notation "invc" hyp(H) :=
  (* Rename H first to free identifier *)
  let _temp := fresh "_temp" in
  rename H into _temp;
  inv _temp;
  (* Some inversions will clear the hypothesis automatically
     (notably inversions on equalities), so we should only `try`
     to clear it. *)
  try clear _temp.

Tactic Notation "invc" hyp(H) "as" simple_intropattern(pat) :=
  let _temp := fresh in 
  rename H into _temp;
  inv _temp as pat;
  try clear _temp.


Tactic Notation "dependent" "destruction" uconstr(c) :=
  fail "To use dependent destruction, first [Require Import Coq.Program.Equality]".
