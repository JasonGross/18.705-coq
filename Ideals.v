Require Import Setoid Ensembles.
Require Export Rings.
Require Import Common Notations.

Set Implicit Arguments.

Local Open Scope ring_unit_scope.

Ltac ideal_pre_simplify req :=
  repeat intro; destruct_head_hnf ex; split_and;
  repeat subst_rel req;
  repeat split; trivial.

Ltac ideal_simplify rth req :=
  repeat match goal with
           | _ => eassumption
           | _ => reflexivity
           | _ => rewrite (Rdistr_r rth _ _)
           | _ => rewrite (Rdistr_l rth)
           | _ => solve [ repeat esplit; try reflexivity; eauto with rings ]
           | _ => ring
           | [ |- req 0 _ ] => symmetry
           | [ |- req (?a + ?b) 0 ] => apply (radd_O_opp rth)
           | _ => abstract eauto with rings
           | _ => solve [ eauto with rings ]
           | _ => rewrite (ring_opp_mul_def rth)
           | _ => progress autorewrite with rings in *
           | _ => repeat subst_rel req
         end.

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

  Local Hint Resolve
        (Rmul_0_l sth rsth rth) (Rmul_0_r rth)
        (Rmul_1_l rth) (Rmul_1_r rth)
        (Radd_0_l rth) (Radd_0_r rth) : rings.

  Local Hint Extern 0 => reflexivity.
  Local Hint Extern 0 => reflexivity : rings.

  Section ideal.
    Record ideal :=
      {
        Rideal :> Ensemble R;
        Rideal_proper : forall a b, a == b -> a ∈ Rideal -> b ∈ Rideal;
        Rideal_O : 0 ∈ Rideal;
        Rideal_add : forall a b, a ∈ Rideal -> b ∈ Rideal -> a + b ∈ Rideal;
        Rideal_lmul : forall x a, a ∈ Rideal -> x * a ∈ Rideal;
        Rideal_rmul : forall x a, a ∈ Rideal -> a * x ∈ Rideal
      }.

    Bind Scope ideal_scope with ideal.

    Section ideal_lemmas.
      Variable Rideal : ideal.

      Definition Rideal_proper' : forall a b, a == b -> a ∈ Rideal -> b ∈ Rideal := Rideal_proper Rideal.
      Definition Rideal_O' : 0 ∈ Rideal := Rideal_O Rideal.
      Definition Rideal_add' : forall a b, a ∈ Rideal -> b ∈ Rideal -> a + b ∈ Rideal := Rideal_add Rideal.
      Definition Rideal_lmul' : forall x a, a ∈ Rideal -> x * a ∈ Rideal := Rideal_lmul Rideal.
      Definition Rideal_rmul' : forall x a, a ∈ Rideal -> a * x ∈ Rideal := Rideal_rmul Rideal.
    End ideal_lemmas.

    Local Hint Immediate @Rideal_O @Rideal_O' : rings.
    Local Hint Resolve @Rideal_O @Rideal_proper @Rideal_add @Rideal_lmul @Rideal_rmul
           @Rideal_O' @Rideal_proper' @Rideal_add' @Rideal_lmul' @Rideal_rmul' : rings.

    Global Instance ideal_proper (A : ideal) : Morphisms.Proper
                                                 (req ==> Basics.impl)
                                                 (fun x => x ∈ A)
      := Rideal_proper A.

    Global Instance ideal_proper_flip (A : ideal) : Morphisms.Proper
                                                      (req ==> Basics.flip Basics.impl)
                                                      (fun x => x ∈ A)
      := (fun a b H => Rideal_proper A (Equivalence_Symmetric _ _ H)).

    Lemma ideal_opp (A : ideal) : forall a, a ∈ A -> -a ∈ A.
      intros a H;
      rewrite (ring_opp_mul_def rth);
      eauto 2 with rings.
    Qed.

    Section add_ideal.
      Variables A B : ideal.

      Let ideal_add_prop := (fun x => exists a b, a ∈ A /\ b ∈ B /\ x == a + b).

      Lemma ideal_add_proper' : forall a b, a == b -> a ∈ ideal_add_prop -> b ∈ ideal_add_prop.
        ideal_pre_simplify req; repeat esplit;
        ideal_pre_simplify req; eauto with rings.
      Qed.

      Local Instance ideal_add_proper : Morphisms.Proper
                                          (req ==> Basics.impl)
                                          (fun x => x ∈ ideal_add_prop)
        := ideal_add_proper'.

      Local Instance ideal_add_proper_flip : Morphisms.Proper
                                               (req ==> Basics.flip Basics.impl)
                                               (fun x => x ∈ ideal_add_prop)
        := (fun a b H => ideal_add_proper (Equivalence_Symmetric _ _ H)).

      Definition ideal_add : ideal.
        refine {|
            Rideal := (fun x => exists a b, a ∈ A /\ b ∈ B /\ x == a + b)
          |};

            ideal_pre_simplify req;
            match goal with
              | [ H0 : ?a0 ∈ (Rideal A), H1 : ?a1 ∈ (Rideal A), H2 : ?b0 ∈ (Rideal B), H3 : ?b1 ∈ (Rideal B) |- ?x ∈ _ ] =>
                let H := fresh in assert (H : x == (a0 + a1) + (b0 + b1)) by ring;
              rewrite H; exists (a0 + a1), (b0 + b1); repeat split; eauto with rings;
              ring
              | _ => solve [ ideal_simplify rth req ]
              | _ => solve [ repeat esplit; ideal_simplify rth req ]
              | _ => idtac
            end.
        repeat esplit; autorewrite with rings; try eassumption; try reflexivity.
        eassumption.
        eauto with rings.
          ).
      Defined.
    End add_ideal.

    Section intersect_ideal.
      Variables A B : ideal.

      Let ideal_intersect_prop := (fun x => x ∈ A /\ x ∈ B).

      Definition ideal_intersection : ideal.
        refine {|
            Rideal := (fun x => x ∈ A /\ x ∈ B)
          |};
        abstract (ideal_pre_simplify req; eauto with rings).
      Defined.
    End intersect_ideal.

    Section mul_ideal.
      Variables A B : ideal.

      Inductive ideal_mul_witness : R -> Prop :=
        | ideal_mul_intro : forall a b, a ∈ A -> b ∈ B -> (a * b) ∈ ideal_mul_witness
        | ideal_mul_proper : forall a b, a == b -> a ∈ ideal_mul_witness -> b ∈ ideal_mul_witness
        | ideal_mul_add : forall x y, x ∈ ideal_mul_witness -> y ∈ ideal_mul_witness -> (x + y) ∈ ideal_mul_witness.

      Local Hint Constructors ideal_mul_witness : rings.

      Local Instance ideal_mul_proper' : Morphisms.Proper
                                          (req ==> Basics.impl)
                                          ideal_mul_witness
        := ideal_mul_proper.

      Local Instance ideal_mul_proper'_flip : Morphisms.Proper
                                                (req ==> Basics.flip Basics.impl)
                                                ideal_mul_witness
        := (fun a b H => ideal_mul_proper (Equivalence_Symmetric _ _ H)).

      Local Hint Extern 5 (ideal_mul_witness _) => constructor : rings.

      Definition ideal_mul : ideal.
        refine {|
            Rideal := (fun x => x ∈ ideal_mul_witness)
          |};
        abstract (
            ideal_pre_simplify req;
            eauto with rings;
            hnf in *;
              try match goal with
                | [ H : ideal_mul_witness _, H' : ideal_mul_witness _ |- _ ] => fail 1
                | [ H : ideal_mul_witness _ |- _ ] => induction H;
                                                     ideal_pre_simplify req;
                                                     try (rewrite (Rmul_assoc rth) || rewrite <- (Rmul_assoc rth));
                                                     ideal_simplify rth req
                | _ => eapply (@ideal_mul_proper (_ * _)); [ | solve [ eauto with rings ] ]; solve [ eauto with rings ]
                | _ => eapply (@ideal_mul_proper (_ * _)); solve [ eauto with rings ]
              end
          ).
      Defined.
    End mul_ideal.

    Section principal_ideal.
      Definition principal_ideal (a : R) : ideal.
        refine {|
            Rideal := (fun x => exists y, x == y * a)
          |};
        intros;
        destruct_head_hnf ex; split_and;
        repeat esplit;
        repeat subst_rel req;
        try reflexivity;
        symmetry;
        eauto with rings;
        (rewrite (Rdistr_l rth); reflexivity)
          || (rewrite (Rdistr_r rth); reflexivity)
          || (try (rewrite (Rmul_assoc rth); reflexivity));
        existentials_to_evars; ring_simplify;
        rewrite (Rmul_comm rth); rewrite <- (Rmul_assoc rth); subst_body; reflexivity.
        (* TODO(jgross): Make this proof more automated *)
      Defined.
    End principal_ideal.

    Section ideals_eq.
      Definition subideal (A B : ideal) := forall x, x ∈ A -> x ∈ B.
      Definition ideals_eq (A B : ideal) := subideal A B /\ subideal B A.

      Local Ltac t :=
        repeat split; repeat intro; unfold ideals_eq, subideal in *; hnf in * |- ; split_and;
        intuition.

      Lemma subideal_trans : Transitive subideal.
        t.
      Qed.

      Lemma subideal_refl : Reflexive subideal.
        t.
      Qed.

      Global Add Parametric Relation : _ subideal
          reflexivity proved by subideal_refl
          transitivity proved by subideal_trans
            as subideal_rel.

      Lemma ideals_eq_refl : Reflexive ideals_eq.
        t.
      Qed.

      Lemma ideals_eq_symm : Symmetric ideals_eq.
        t.
      Qed.

      Lemma ideals_eq_trans : Transitive ideals_eq.
        t.
      Qed.

      Global Add Parametric Relation : _ ideals_eq
          reflexivity proved by ideals_eq_refl
          symmetry proved by ideals_eq_symm
          transitivity proved by ideals_eq_trans
            as ideals_eq_rel.

      Lemma subideal_antisymm : Antisymmetric _ ideals_eq subideal.
        t.
      Qed.

      Global Add Parametric Morphism : ideal_add
          with signature ideals_eq ==> ideals_eq ==> ideals_eq
            as ideal_add_mor.
      t;
        ideal_pre_simplify req;
        repeat esplit; try reflexivity;
        intuition.
      Qed.

      Global Add Parametric Morphism : ideal_mul
          with signature ideals_eq ==> ideals_eq ==> ideals_eq
            as ideal_mul_mor.
      t;
        hnf in *; match goal with | [ H : ideal_mul_witness _ _ _ |- _ ] => induction H end;
        ideal_pre_simplify req;
        change (ideal_mul_witness ?a ?b) with (Rideal (ideal_mul a b)) in *;
        change ((Rideal (ideal_mul ?a ?b)) ?x) with (x ∈ (ideal_mul a b)) in *;
        try solve [
              repeat esplit; try reflexivity;
              intuition; try solve [ constructor; intuition ]
            ];
        ideal_simplify rth req.
      Qed.

      Global Add Parametric Morphism : ideal_intersection
          with signature subideal ==> subideal ==> subideal
            as ideal_intersection_subideal_mor.
      t.
      Qed.

      Global Add Parametric Morphism : ideal_intersection
          with signature ideals_eq ==> ideals_eq ==> ideals_eq
            as ideal_intersection_mor.
      t.
      Qed.
    End ideals_eq.

    Local Infix "*" := ideal_mul : ideal_scope.
    Local Infix "+" := ideal_add : ideal_scope.
    Local Notation "⟨ x ⟩" := (principal_ideal x).

    Definition semi_ring_of_ideals : @semi_ring_theory ideal (⟨ 0 ⟩) (⟨ 1 ⟩) ideal_add ideal_mul ideals_eq.
      constructor; t;
      ideal_pre_simplify req; simpl in *;
      destruct_head_hnf ex;
      repeat match goal with
               | [ H : _ |- _ ] => ring_simplify in H
             end;
      split_and; simpl;
      repeat subst_rel req.
      - rewrite (Radd_0_l rth); assumption.
      - hnf.
        repeat esplit;
        existentials_to_evars;
        try ring_simplify;
          subst_body; reflexivity || (try eassumption);
          ring.
      - simpl; hnf; subst_rel req; repeat esplit; eauto with rings; ring.
      - simpl; hnf; subst_rel req; repeat esplit; eauto with rings; ring.
      - repeat esplit; try eassumption; try reflexivity; repeat subst_rel req; ring.
      - repeat esplit; try eassumption; try reflexivity; repeat subst_rel req; ring.
      - repeat esplit; try eassumption; try reflexivity; hnf in * |- ;
        match goal with | [ H : ideal_mul_witness _ _ _ |- _ ] => induction H end;
        eauto with rings.
      - repeat esplit; try eassumption; try reflexivity; repeat subst_rel req.
        ideal_pre_simplify req. econstructor; try constructor; repeat esplit; try eassumption;
                                existentials_to_evars; ring_simplify; subst_body; try reflexivity;
                                eauto with rings.
      - repeat esplit; try eassumption; try reflexivity; hnf in * |- ;
        match goal with | [ H : ideal_mul_witness _ _ _ |- _ ] => induction H end;
        eauto with rings; ideal_pre_simplify req;
        existentials_to_evars in *; ring_simplify; subst_body; try ring;
        existentials_to_evars in *;
        do 2 try match goal with
                 | [ H : _ |- _ ] => progress ring_simplify in H
               end.
        ideal_pre_simplify req.
        pose (Rdistr_l rth).
        match goal with
           | _ => eassumption
           | _ => reflexivity
           | _ => rewrite (Rdistr_r rth sth rsth)
           | _ => rewrite (Rdistr_l rth)
           | _ => solve [ repeat esplit; try reflexivity; eauto with rings ]
           | _ => ring
           | [ |- req 0 _ ] => symmetry
           | [ |- req (?a + ?b) 0 ] => apply (radd_O_opp rth)
           | _ => abstract eauto with rings
           | _ => solve [ eauto with rings ]
           | _ => rewrite (ring_opp_mul_def rth)
           | _ => progress autorewrite with rings in *
           | _ => repeat subst_rel req
         end.


        solve [ ideal_simplify rth req ].
        ideal_pre_simplify req.

        existentials_to_evars in *.
existentials_to_evars_in_hyps.

IHideal_mul_witness.
Ltac existentials_to_evars_in_hyps :=
  do 1 match goal with
           | [ H : context[?x] |- _ ] => existential_to_evar x
         end.
existentials_to_evars_in_hyps.
        existentials_to_evars_in IHideal_mul_witness.
        ring_simplify in IHideal_mul_witness.
          match goal with
            | [ H : req ?a ?b |- _ ] => (first [ atomic a | fail "variable" a "is not atomic" ]; subst_by_rewrite_hyp a H)
                                          || (first [ atomic b | fail "variable" b "is not atomic" ]; subst_by_rewrite_rev_hyp b H)
          end.

        subst_rel req.
        ideal_simplify rth req.

        hnf in *.
        destruct
        ideal_pre_simplify req. econstructor; try constructor; repeat esplit; try eassumption;
                                existentials_to_evars; ring_simplify; subst_body; try reflexivity;
                                eauto with rings.
      - repeat esplit; try eassumption; try reflexivity; repeat subst_rel req; ring.
        SearchAbout (_ == _ * _).
        destruct rth.
        Focus 2.
        hnf.
        constructor.
 eapply (@ideal_mul_proper _ (_ * _)).


        ideal_pre_simplify req.
        destruct_head_hnf ideal_mul_witness; eauto with rings.
        hnf in H.
        destruct H.
        eauto with rings.
        ideal_pre_simplify req.
        hnf in H.
        compute in H.
 ring_simplify in H.
 ideal_simplify rth req.  repeat subst_rel req.
        hnf in * |- .
        induction H.
        ideal_simplify rth req.

 ring.






 ring_simplify.
      hnf in * |- .
      repeat intro.

      hnf in H.
      simpl in *.

      ring_simplify [rth] in H.
      compute in H.
      compute.
      hnf.
      compute.
      Print semi_ring_theory.


    Definition ring_of_ideals : Ring_
  End ideal.
End ring.

Bind Scope ideal_scope with ideal.

Notation "u ⁻¹" := (Runit_inverse u) : ring_unit_scope.

Print Runit_inverse.

Notation "u ⁻¹" := (Runit_inverse u).

Hint Immediate @Rideal_O : rings.
Hint Resolve @Rideal_proper @Rideal_add @Rideal_lmul @Rideal_rmul : rings.

    Local Hint Immediate @Rideal_O @Rideal_O' : rings.
    Local Hint Resolve @Rideal_O @Rideal_proper @Rideal_add @Rideal_lmul @Rideal_rmul
           @Rideal_O' @Rideal_proper' @Rideal_add' @Rideal_lmul' @Rideal_rmul' : rings.
