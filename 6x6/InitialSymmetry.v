From Stdlib Require Import List NArith ZArith Lia.
From TPP2026.Six Require Import Rules Bounds Dag Symmetry.
Import ListNotations.

Definition first8 := claim_board (Claim 1097984 2097152 White).

Definition first13 := transform transposition first8.

Definition first27 := transform rotation first8.

Definition first22 := transform rotation first13.

Lemma first8_well_formed : well_formed first8.
Proof. reflexivity. Qed.

Lemma initial_moves : moves initial6 Black =
  [(8, first8); (13, first13); (22, first22); (27, first27)].
Proof. vm_compute; reflexivity. Qed.

Theorem initial_upper_from_first8 : forall z,
  upper_bound first8 White z -> upper_bound initial6 Black z.
Proof.
  intros z H8.
  assert (H13 : upper_bound first13 White z).
  { apply upper_bound_symmetry; [exact first8_well_formed|exact H8]. }
  assert (H27 : upper_bound first27 White z).
  { apply upper_bound_symmetry; [exact first8_well_formed|exact H8]. }
  assert (H22 : upper_bound first22 White z).
  { apply upper_bound_symmetry; [apply transform_well_formed|exact H13]. }
  change (forces White (fun b =>
    (black_score b <= z)%Z) initial6 (other White)).
  apply force_all; cbn [other].
  - exists 8, first8. apply moves_spec. rewrite initial_moves. simpl. auto.
  - intros s b Hmove. apply moves_spec in Hmove. rewrite initial_moves in Hmove.
    simpl in Hmove. destruct Hmove as [H|[H|[H|[H|[]]]]]; inversion H; subst;
      assumption.
Qed.
Print Assumptions initial_upper_from_first8.

Lemma forces_weaken : forall who goal1 goal2,
  (forall b, goal1 b -> goal2 b) -> forall b p,
  forces who goal1 b p -> forces who goal2 b p.
Proof.
  intros who goal1 goal2 Hgoal b p H. induction H.
  - apply force_end; auto.
  - eapply force_choose; eauto.
  - apply force_all; auto.
  - apply force_pass; auto.
Qed.

Corollary initial_white_win_from_first8 : upper_bound first8 White (-1) ->
  forces White white_ahead initial6 Black.
Proof.
  intro H. pose proof (initial_upper_from_first8 (-1) H) as Hinit.
  eapply forces_weaken; [|exact Hinit].
  intros b Hb. unfold black_score in Hb. unfold white_ahead. lia.
Qed.
Print Assumptions initial_white_win_from_first8.
