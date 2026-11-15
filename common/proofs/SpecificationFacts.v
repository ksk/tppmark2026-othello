From Stdlib Require Import List Bool Arith Lia.
From TPP2026.Common Require Import Rules Specification.
Import ListNotations.

(** The relational specification and the executable rules agree. *)
Module Make (P : Rules.Pieces) (D : Rules.Dimension).
Module S := Specification.Make P D.
Include S.
Import P.

Lemma bracketed_sound b p xs captured :
  bracketed b p xs captured -> bracket b p xs = Some captured.
Proof.
  intro captured_run.
  induction captured_run as
    [s rest own_stone|s rest captured opponent_stone captured_tail IHtail].
  - cbn [bracket].
    rewrite own_stone.
    now destruct p.
  - cbn [bracket].
    rewrite opponent_stone.
    destruct p; cbn [other same_player]; now rewrite IHtail.
Qed.

Lemma bracketed_complete b p xs : forall captured,
  bracket b p xs = Some captured -> bracketed b p xs captured.
Proof.
  induction xs as [|s rest IHrest]; intros captured bracket_ok.
  - now discriminate.
  - cbn [bracket] in bracket_ok.
    destruct (cell_at b s) as [|q] eqn:square_contents; [discriminate|].
    destruct p, q; cbn [same_player] in bracket_ok.
    + inversion bracket_ok; subst.
      now apply bracket_stop.
    + destruct (bracket b Black rest) as [ys|] eqn:tail_ok; [|discriminate].
      inversion bracket_ok; subst.
      apply bracket_extend; [exact square_contents|].
      now apply IHrest.
    + destruct (bracket b White rest) as [ys|] eqn:tail_ok; [|discriminate].
      inversion bracket_ok; subst.
      apply bracket_extend; [exact square_contents|].
      now apply IHrest.
    + inversion bracket_ok; subst.
      now apply bracket_stop.
Qed.

(** Captured squares form a run of opposing stones immediately followed
    by a friendly stone. A legal placement requires a nonempty run. *)

Lemma bracketed_prefix b p xs captured :
  bracketed b p xs captured -> exists endpoint rest,
    xs = captured ++ endpoint :: rest /\
    Forall (fun t => cell_at b t = Stone (other p)) captured /\
    cell_at b endpoint = Stone p.
Proof.
  intro captured_run.
  induction captured_run as
    [s rest own_stone|s rest captured opponent_stone captured_tail IHtail].
  - exists s, rest.
    now repeat split; auto.
  - destruct IHtail as
      [t [tail [ray_shape [opponent_stones own_stone]]]].
    exists t, tail.
    split; [simpl; now rewrite ray_shape|].
    split; [now constructor|exact own_stone].
Qed.

Lemma flips_spec b p s t : In t (flips b p s) <-> captures b p s t.
Proof.
  unfold flips, captures.
  rewrite in_flat_map.
  split.
  - intros [d [direction_ok square_captured]].
    unfold captured_in in square_captured.
    destruct (bracket b p (ray (side - 1) s d)) as [xs|]
      eqn:bracket_ok; [|contradiction].
    exists d, xs.
    split; [exact direction_ok|].
    split; [now apply bracketed_complete|exact square_captured].
  - intros [d [xs [direction_ok [captured_run square_captured]]]].
    exists d.
    split; [exact direction_ok|].
    unfold captured_in.
    rewrite (bracketed_sound _ _ _ _ captured_run).
    exact square_captured.
Qed.

Lemma existsb_nat_eqb t xs :
  existsb (Nat.eqb t) xs = true <-> In t xs.
Proof.
  rewrite existsb_exists.
  split.
  - intros [u [member same_square]].
    apply Nat.eqb_eq in same_square.
    now subst.
  - intro member.
    exists t.
    split; [exact member|exact (Nat.eqb_refl t)].
Qed.

Lemma membership_bool xs ys :
  (forall t, In t xs <-> In t ys) ->
  forall t, existsb (Nat.eqb t) xs = existsb (Nat.eqb t) ys.
Proof.
  intros same_members t.
  destruct (existsb (Nat.eqb t) xs) eqn:in_xs,
    (existsb (Nat.eqb t) ys) eqn:in_ys; try reflexivity; exfalso.
  - apply existsb_nat_eqb in in_xs.
    apply same_members in in_xs.
    apply existsb_nat_eqb in in_xs.
    now congruence.
  - apply existsb_nat_eqb in in_ys.
    apply same_members in in_ys.
    apply existsb_nat_eqb in in_ys.
    now congruence.
Qed.

Theorem play_spec b p s b' :
  play b p s = Some b' <-> legal_spec b p s b'.
Proof.
  split.
  - intro move_ok.
    unfold play in move_ok.
    destruct (s <? area) eqn:square_ok; [|discriminate].
    destruct (cell_at b s) eqn:empty_square; [|discriminate].
    destruct (flips b p s) as [|x xs] eqn:captured_squares; [discriminate|].
    injection move_ok as <-.
    exists (x :: xs).
    split; [now apply Nat.ltb_lt|].
    split; [exact empty_square|].
    split; [discriminate|].
    split; [|reflexivity].
    intro t.
    rewrite <- captured_squares.
    exact (flips_spec b p s t).
  - intros [xs [square_ok [empty_square [nonempty [captures_xs board_shape]]]]].
    assert (same_members : forall t, In t xs <-> In t (flips b p s)) by
      (intro t; rewrite captures_xs; symmetry; exact (flips_spec b p s t)).
    assert (flips_nonempty : flips b p s <> []).
    + intro no_flips.
      destruct xs as [|x xs]; [contradiction|].
      assert (member : In x (x :: xs)) by (simpl; auto).
      apply same_members in member.
      rewrite no_flips in member.
      now contradiction.
    + assert (updated_board : b' = put_and_flip b p s (flips b p s)) by
        (rewrite board_shape; unfold put_and_flip; apply map_ext; intro t;
         now rewrite (membership_bool _ _ same_members t)).
      rewrite updated_board.
      unfold play.
      apply Nat.ltb_lt in square_ok.
      rewrite square_ok, empty_square.
      now destruct (flips b p s); [contradiction|reflexivity].
Qed.

End Make.
