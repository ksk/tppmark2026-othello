From Stdlib Require Import List Bool Arith Lia.
From TPP2026.Common Require Import Rules.
Import ListNotations.

(** Basic facts about the common rules in common/Rules.v. *)
Module Make (P : Rules.Pieces) (D : Rules.Dimension).
Module R := Rules.Make P D.
Include R.
Import P.

Lemma play_in_range b p s b' :
  play b p s = Some b' -> In s squares.
Proof.
  intro move_ok.
  unfold play in move_ok.
  destruct (s <? area) eqn:square_ok; [|discriminate].
  apply Nat.ltb_lt in square_ok.
  unfold squares.
  apply in_seq.
  now lia.
Qed.

Lemma play_well_formed b p s b' :
  play b p s = Some b' -> well_formed b'.
Proof.
  intro move_ok.
  unfold play in move_ok.
  destruct (s <? area); [|discriminate].
  destruct (cell_at b s); [|discriminate].
  destruct (flips b p s); [discriminate|].
  injection move_ok as <-.
  unfold well_formed, put_and_flip, squares.
  now rewrite length_map, length_seq.
Qed.

Lemma moves_spec b p s b' :
  In (s, b') (moves b p) <-> legal_move b p s b'.
Proof.
  unfold moves, legal_move.
  rewrite in_flat_map.
  split.
  - intros [t [square_ok in_moves]].
    destruct (play b p t) as [c|] eqn:move_ok.
    + simpl in in_moves.
      destruct in_moves as [same_move|[]].
      inversion same_move; subst.
      now auto.
    + now contradiction.
  - intros [square_ok move_ok].
    exists s.
    split; [exact square_ok|].
    rewrite move_ok.
    now simpl; auto.
Qed.

Lemma no_moveb_spec b p : no_moveb b p = true <-> no_move b p.
Proof.
  unfold no_moveb, no_move.
  destruct (moves b p) as [|[s c] rest] eqn:move_list.
  - split; [|reflexivity].
    intros _ t c' move_legal.
    apply moves_spec in move_legal.
    rewrite move_list in move_legal.
    now contradiction.
  - split; [discriminate|].
    intro no_legal_move.
    exfalso.
    apply (no_legal_move s c).
    apply moves_spec.
    rewrite move_list.
    now simpl; auto.
Qed.

Lemma has_moveb_spec b p :
  negb (no_moveb b p) = true <-> has_move b p.
Proof.
  unfold no_moveb, has_move.
  destruct (moves b p) as [|[s c] rest] eqn:move_list; simpl.
  - split; [discriminate|].
    intros [t [c' move_legal]].
    apply moves_spec in move_legal.
    rewrite move_list in move_legal.
    now contradiction.
  - split.
    + intros _.
      exists s, c.
      apply moves_spec.
      rewrite move_list.
      now simpl; auto.
    + now intros _.
Qed.

Lemma transition_preserves_board b p b' q :
  well_formed b -> transition b p b' q -> well_formed b'.
Proof.
  intros board_ok step_ok.
  destruct step_ok as [b p s b' [_ move_ok]|b p no_move move_exists].
  - exact (play_well_formed b p s b' move_ok).
  - exact board_ok.
Qed.

Lemma initial_well_formed : well_formed initial.
Proof.
  unfold initial, well_formed, squares.
  now rewrite length_map, length_seq.
Qed.

End Make.
