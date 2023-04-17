From Coq Require Import Sorting.Permutation List.
From Coq Require Import Classes.Morphisms.
Import ListNotations.

Class Dec (A : Type) :=
  eq_dec : forall (x y : A), { x = y } + { x <> y }.
Infix "=?" := eq_dec (at level 80).

Definition Multiset (A : Type) : Type :=
  list A.

Definition equ {A} (M1 M2 : Multiset A) :=
  Permutation M1 M2.
Infix "≡" := equ (at level 80).

Goal [1] ≡ [1].
  repeat constructor.
Qed.

Fixpoint count {A} `{Dec A} (a : A) (M : Multiset A) :=
  match M with
  | [] => 0
  | x::M =>
    if x =? a then 1 + count a M else count a M
  end.

Definition empty {A} : Multiset A := [].

Definition union {A} (M1 M2 : Multiset A) := M1 ++ M2.

Definition singleton {A} (a : A) : Multiset A := [a].

Inductive GtExt1 {A} (gt : A -> A -> Prop) (M1 M2 : Multiset A) : Prop :=
  | ext1_intro (X Y : Multiset A) (a : A):
    M1 ≡ a::X ->
    M2 ≡ Y ++ X ->
    (forall y, In y Y -> gt a y) ->
    GtExt1 gt M1 M2.

Definition remove_all {A} `{Dec A} (a : A) (M : Multiset A) :=
  remove eq_dec a M.

Fixpoint remove_one {A} `{Dec A} (a : A) (M : Multiset A) :=
  match M with
  | [] => []
  | x::M =>
    if a =? x then M else x::remove_one a M
  end.

Definition remove_one_eq {A} `{DEC : Dec A} :
  forall (a : A) (M1 M2 : Multiset A),
    M1 ≡ M2 -> remove_one a M1 ≡ remove_one a M2.
Proof.
  intros.
  induction H; simpl.
  - reflexivity.
  - destruct (a =? x) as [->|Hneq]; auto.
    now rewrite IHPermutation.
  - destruct (a =? y) as [->|Hneq1].
    destruct (y =? x) as [->|Hneq1]; try easy.
    destruct (a =? x) as [->|Hneq2]; try easy.
    constructor.
  - now rewrite IHPermutation1, IHPermutation2.
Qed.

Definition remove_all_eq {A} `{DEC : Dec A} :
  forall (a : A) (M1 M2 : Multiset A),
    M1 ≡ M2 -> remove_all a M1 ≡ remove_all a M2.
Proof.
  intros.
  induction H.
  - constructor.
  - simpl. destruct (a =? x) as [->|Hneq]; auto.
    apply Permutation_cons; auto.
  - simpl. destruct (a =? x) as [->|Hneq].
    + destruct (x =? y) as [->|Hneq]; reflexivity.
    + destruct (a =? y) as [->|Hneq']. reflexivity.
      constructor.
  - now rewrite IHPermutation1, IHPermutation2.
Qed.

Definition rem_cons_eq {A} `{DEC : Dec A} :
  forall (a : A) (M1 M2 : Multiset A),
    M1 ≡ a::M2 -> remove_one a M1 ≡ M2.
Proof.
  intros.
  rewrite remove_one_eq; eauto.
  simpl. now destruct (a =? a) as [Heq|Hneq].
Qed.

Lemma GtExt1_inv {A} `{DEC : Dec A}:
  forall gt (M1 M2 : Multiset A) (a : A),
    GtExt1 gt (a::M1) M2 ->
    exists M',
      (M2 ≡ a::M' /\ GtExt1 gt M1 M') \/
      (M2 ≡ M' ++ M1 /\ forall x, In x M' -> gt a x).
Proof.
  intros.
  inversion H as [X Y b H1 H2 H3].
  destruct (a =? b) as [->|Hneq].
  - apply Permutation_cons_inv in H1.
    exists Y. right. split; auto.
    now rewrite H1.
  - pose proof (H4 := rem_cons_eq _ _ _ H1).
    simpl in H4. destruct (b =? a) as [->|_]; try easy.
    rewrite <- H4 in H2.
    exists (Y ++ remove_one b M1). left.
    split.
    + rewrite H2.
      fold ([a] ++ remove_one b M1).
      fold ([a] ++ (Y ++ remove_one b M1)).
      apply Permutation_app_swap_app.
    + eapply (ext1_intro _ _ _ _ _ b).
      symmetry in H1. apply rem_cons_eq in H1.
      rewrite <- H1. simpl.
      destruct (a =? b) as [->|_]; try easy.
      symmetry in H4. apply rem_cons_eq in H4.
      now rewrite H4.
      auto.
Qed.

Definition LtExt1 {A} `{DEC : Dec A} gt (M1 M2 : Multiset A) :=
  GtExt1 gt M2 M1.

#[global]
Instance GtMorphism {A} `{DEC : Dec A} {gt : A -> A -> Prop} :
  Proper (equ ==> equ ==> iff) (LtExt1 gt).
Proof.
  intros X1 X2 HX Y1 Y2 HY. split.
  - intros H. unfold LtExt1 in *.
    inversion H. econstructor.
    rewrite <- HY. apply H0.
    rewrite <- HX. apply H1.
    auto.
  - intros H. unfold LtExt1 in *.
    inversion H. econstructor.
    rewrite HY. apply H0.
    rewrite HX. apply H1.
    auto.
Qed.

#[global]
Instance AccMorphism {A} `{DEC : Dec A} {gt : A -> A -> Prop} :
  Proper (equ ==> iff) (Acc (LtExt1 gt)).
Proof.
  intros X Y H. split.
  - intros Hacc. constructor.
    intros Z HZ. inversion Hacc as [Hacc'].
    apply Hacc'. now rewrite H.
  - intros Hacc. constructor.
    intros Z HZ. inversion Hacc as [Hacc'].
    apply Hacc'. now rewrite <- H.
Qed.

Lemma LtExt1_Acc_cons {A} `{DEC : Dec A} :
  forall gt (M0 : Multiset A) (a : A),
    Acc (LtExt1 gt) M0 ->
    (forall b M, gt a b -> Acc (LtExt1 gt) M -> Acc (LtExt1 gt) (b::M)) ->
    (forall M, LtExt1 gt M M0 -> Acc (LtExt1 gt) (a::M)) ->
    Acc (LtExt1 gt) (a::M0).
Proof.
  intros * Hacc H1 H2.
  constructor. intros N [M' [HN1 | HN2]]%GtExt1_inv.
  - destruct HN1 as [H3 H4].
    rewrite H3. apply H2, H4.
  - destruct HN2 as [H3 H4].
    rewrite H3. clear H3.
    induction M'; simpl in *; auto.
Qed.

Lemma lemma_14 {A} `{DEC : Dec A} :
  forall (gt : A -> A -> Prop) (a : A),
    (forall (b : A) (M : Multiset A), gt a b -> Acc (LtExt1 gt) M -> Acc (LtExt1 gt) (b::M)) ->
    forall M, Acc (LtExt1 gt) M -> Acc (LtExt1 gt) (a::M).
Proof.
  intros * H M HM.
  induction HM as [M' H1 H2].
  apply LtExt1_Acc_cons; auto.
  now constructor.
Qed.

Lemma lemma_15 {A} `{DEC : Dec A} :
  forall (gt : A -> A -> Prop) (a : A),
    Acc (fun x y => gt y x) a ->
    forall (M : Multiset A), Acc (LtExt1 gt) M -> Acc (LtExt1 gt) (a::M).
Proof.
  intros gt a Ha.
  induction Ha as [b H1 H2].
  intros M HM.
  apply lemma_14; auto.
Qed.

Lemma lemma_16 {A} `{DEC : Dec A} :
  forall (gt : A -> A -> Prop),
    well_founded (fun x y => gt y x) ->
    well_founded (LtExt1 gt).
Proof.
  intros * Hwf M.
  induction M.
  - constructor. intros M' Hl.
    inversion Hl as [X Y a H1 H2 H3].
    now apply Permutation_nil_cons in H1.
  - apply lemma_15; auto.
Qed.
