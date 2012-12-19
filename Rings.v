Require Import Setoid.
Require Export Ring Ring_theory Ensembles.
Require Import Common Notations.

Set Implicit Arguments.

Local Open Scope ring_unit_scope.

Create HintDb rings.

Section ring.
  Variable R : Type.
  Variables rO rI : R.
  Variables radd rmul rsub : R -> R -> R.
  Variable ropp : R -> R.
  Variables req : R -> R -> Prop.

  Variable rth : @ring_theory R rO rI radd rmul rsub ropp req.
  Variable sth : @Equivalence R req.
  Variable rsth : @Ring_theory.ring_eq_ext R radd rmul ropp req.

  Add Parametric Relation : _ req
      reflexivity proved by Equivalence_Reflexive
      symmetry proved by Equivalence_Symmetric
      transitivity proved by Equivalence_Transitive
        as req_rel.

  Add Parametric Morphism : radd
      with signature req ==> req ==> req
        as radd_mor.
    destruct rsth; assumption.
  Qed.

  Add Parametric Morphism : rmul
      with signature req ==> req ==> req
        as rmul_mor.
    destruct rsth; assumption.
  Qed.

  Add Parametric Morphism : ropp
      with signature req ==> req
        as ropp_mor.
    destruct rsth; assumption.
  Qed.

  Add Parametric Morphism : rsub
      with signature req ==> req ==> req
        as rsub_mor.
    intros; repeat rewrite (Rsub_def rth);
    apply (Radd_ext rsth); destruct rsth; eauto.
  Qed.

  Add Ring ring_R : rth. (* (setoid sth rsth). *)

  Local Infix "+" := radd.
  Local Infix "-" := rsub.
  Local Infix "*" := rmul.
  Local Notation "- a" := (ropp a).
  Local Infix "==" := req.
  Local Notation "x == y == z" := (x == y /\ y == z).
  Local Notation "x <> y" := (not (x == y)).

  Local Notation "0" := rO.
  Local Notation "1" := rI.

  Lemma radd_O_opp a b : a = -b -> a + b == 0.
    intro x; subst; ring.
  Qed.

  Lemma Rdistr_r : forall x y z : R, x * (y + z) == x * y + x * z.
    intros; ring.
  Qed.

  Lemma rmul_x_O : forall x, x * 0 == 0.
    intros; ring.
  Qed.

  Lemma rmul_O_x : forall x, 0 * x == 0.
    intros; ring.
  Qed.

  Hint Resolve @rmul_x_O @rmul_O_x : rings.
  Hint Rewrite @rmul_x_O @rmul_O_x : rings.

  Record Runit :=
    {
      Runit_value :> R;
      Runit_inverse_value : R;
      Runit_inverse_is_right_inverse : Runit_value * Runit_inverse_value == 1;
      Runit_inverse_is_left_inverse : Runit_inverse_value * Runit_value == 1
    }.

  Bind Scope ring_unit_scope with Runit.

  Definition Runit_inverse (u : Runit) : Runit :=
    {|
      Runit_value := u.(Runit_inverse_value);
      Runit_inverse_value := u.(Runit_value);
      Runit_inverse_is_right_inverse := u.(Runit_inverse_is_left_inverse);
      Runit_inverse_is_left_inverse := u.(Runit_inverse_is_right_inverse)
    |}.

  Notation "u ⁻¹" := (Runit_inverse u) : ring_unit_scope.

  Definition rdiv (a : R) (b : Runit) := a * (b ⁻¹).

  Local Infix "/" := rdiv.

  Lemma ring_opp_mul_def a : -a == (-(1)) * a.
    ring.
  Qed.
End ring.

Bind Scope ring_unit_scope with Runit.

Notation "u ⁻¹" := (Runit_inverse u) : ring_unit_scope.
