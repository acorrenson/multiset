From Coq Require Import Sorting.Permutation List.
From Coq Require Import Classes.Morphisms.
Import ListNotations.

(** * A minimalist and self contained formalization of multiset ordering *)

Section MSO.

(** ** Definitions *)

(** We start with a base type [A] equiped with a binary relation [lt] *)
Context {A : Type} {lt : A -> A -> Prop}.

(** We suppose that [A] has a decidable equality *)
Context {eq_dec : forall (x y : A), { x = y } + { x <> y }}.

Definition equ (L1 L2 : list A) :=
  Permutation L1 L2.
Infix "≡" := (Permutation) (at level 80).
Infix "=?" := (eq_dec) (at level 80).

(** We extend [lt] to a binary relation on lists
    Intuitively [lt_ext1 L1 L2] iff L1 is obtained 
    from L2 by removing an element and
    replacing it by a list of smaller ones
*)
Inductive lt_ext1 (L1 L2 : list A) : Prop :=
  | lt_ext1_intro x X Y :
    L1 ≡ Y ++ X ->
    L2 ≡ x::X ->
    (forall y, In y Y -> lt y x) ->
    lt_ext1 L1 L2.

(** Removing one occurence of [x] in [L] *)
Fixpoint remove (L : list A) (x : A) :=
  match L with
  | [] => []
  | y::L =>
    if x =? y then L else y::remove L x
  end.

(** [remove] is compatible with permutations *)
#[global]
Instance remove_morphism: Proper (equ ==> eq ==> equ) remove.
Proof.
  intros L1 L2 Heq a ? <-.
  induction Heq; simpl.
  - reflexivity.
  - destruct (eq_dec a x) as [->|Hne]; auto.
    now rewrite IHHeq.
  - destruct (eq_dec a x) as [->|Hne1].
    destruct (eq_dec x y) as [->|Hne2]; try easy.
    destruct (eq_dec a y) as [->|Hne2]; try easy.
    constructor.
  - now rewrite IHHeq1, IHHeq2.
Qed.

Lemma remove_head:
  forall a L, L ≡ remove (a::L) a.
Proof.
  intros; simpl.
  now destruct (eq_dec a a).
Qed.

(** ** Proof that [lt_ext1] is well founded *)

Theorem lt_ext1_inv:
  forall L1 L2 a,
    lt_ext1 L1 (a::L2) ->
    exists X,
      (L1 ≡ a::X /\ lt_ext1 X L2) \/
      (L1 ≡ X ++ L2 /\ forall x, In x X -> lt x a).
Proof.
  intros L1 L2 a H.
  inversion H as [b X Y HXY Heq HY].
  destruct (eq_dec a b) as [->|Hne].
  - apply Permutation_cons_inv in Heq.
    exists Y. right. now rewrite Heq.
  - pose proof (Heq' := remove_morphism _ _ Heq b b eq_refl).
    simpl in Heq'.
    destruct (eq_dec b b) as [_|]; try easy.
    destruct (eq_dec b a) as [->|_]; try easy.
    rewrite <- Heq' in HXY.
    exists (Y ++ remove L2 b).
    left. split.
  + rewrite HXY.
    fold ([a] ++ remove L2 b).
    fold ([a] ++ (Y ++ remove L2 b)).
    apply Permutation_app_swap_app.
  + econstructor; eauto.
    rewrite <- Heq' in Heq.
    eapply Permutation_cons_inv.
    rewrite Heq. econstructor.
Qed.

#[global]
Instance lt_ext1_morphism:
  Proper (equ ==> equ ==> iff) lt_ext1.
Proof.
  intros X1 X2 HX Y1 Y2 HY. split.
  - intros H. inversion H. econstructor.
    rewrite <- HX. apply H0.
    rewrite <- HY. apply H1.
    auto.
  - intros H. inversion H. econstructor.
    rewrite HX. apply H0.
    rewrite HY. apply H1.
    auto.
Qed.

Lemma helper_1:
  forall (L1 : list A) (a : A),
    (forall b L2, lt b a -> Acc lt_ext1 L2 -> Acc lt_ext1 (b::L2)) ->
    (forall L2, lt_ext1 L2 L1 -> Acc lt_ext1 (a::L2)) ->
    Acc lt_ext1 L1 ->
    Acc lt_ext1 (a::L1).
Proof.
  intros * H1 H2 Hacc.
  constructor. intros N [M' [HN1 | HN2]]%lt_ext1_inv.
  - destruct HN1 as [H3 H4].
    rewrite H3. apply H2, H4.
  - destruct HN2 as [H3 H4].
    rewrite H3. clear H3.
    induction M'; simpl in *; auto.
Qed.

Lemma helper_2:
  forall a,
    (forall (b : A) (M : list A), lt b a -> Acc lt_ext1 M -> Acc lt_ext1 (b::M)) ->
    forall M, Acc lt_ext1 M -> Acc lt_ext1 (a::M).
Proof.
  intros * H M HM.
  induction HM as [M' H1 H2].
  apply helper_1; auto.
  now constructor.
Qed.

Lemma helper_3:
  forall (a : A) (M : list A),
    Acc lt a -> Acc lt_ext1 M -> Acc lt_ext1 (a::M).
Proof.
  intros a M Ha.
  induction Ha as [b H1 H2] in M |-*.
  intros HM. apply helper_2; auto.
Qed.

Lemma well_founded_lt_ext1:
    well_founded lt ->
    well_founded lt_ext1.
Proof.
  intros * Hwf M.
  induction M.
  - constructor. intros M' Hl.
    inversion Hl as [X Y a H1 H2 H3].
    now apply Permutation_nil_cons in H2.
  - apply helper_3; auto.
Qed.

End MSO.