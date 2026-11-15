From Stdlib Require Import List Bool Arith Lia NArith.
From TPP2026.Six Require Import Rules Bounds Dag FastDag FastDecode NatBits.
Import ListNotations.

Definition bit_cell (c : claim) (s : nat) : cell :=
  if N.testbit_nat (black_bits c) s then Stone Black
  else if N.testbit_nat (white_bits c) s then Stone White else Empty.

Lemma bit_cell_correct : forall c s, s < 36 ->
  bit_cell c s = cell_at (claim_board c) s.
Proof.
  intros c s H. unfold bit_cell. rewrite !testbit_nat_correct.
  unfold cell_at, claim_board, squares.
  set (f := fun i =>
    if N.testbit (black_bits c) (N.of_nat i) then Stone Black
    else if N.testbit (white_bits c) (N.of_nat i) then Stone White
    else Empty).
  change (f s = nth s (map f (seq 0 36)) Empty).
  rewrite (nth_indep _ Empty (f 0)) by (rewrite length_map, length_seq;
    exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Fixpoint bit_bracket (c : claim) (p : player)
    (xs : list nat) : option (list nat) :=
  match xs with
  | [] => None
  | s :: rest =>
      match bit_cell c s with
      | Empty => None
      | Stone q =>
          if same_player p q then Some []
          else match bit_bracket c p rest with None => None
               | Some ys => Some (s :: ys)
               end
      end
  end.

Lemma bit_bracket_correct : forall c p xs, Forall (fun s => s < 36) xs ->
  bit_bracket c p xs = bracket (claim_board c) p xs.
Proof.
  intros c p xs H. induction H; simpl; [reflexivity|].
  rewrite bit_cell_correct by assumption. rewrite IHForall. reflexivity.
Qed.

Lemma cached_rays_range : forall s, s < 36 ->
  Forall (Forall (fun t => t < 36)) (cached_rays s).
Proof.
  intros s H.
  assert (E : forallb (forallb (fun t => t <? 36)) (cached_rays s) = true).
  { do 36 (destruct s as [|s]; [reflexivity|]). lia. }
  apply Forall_forall. intros xs Hxs. apply forallb_forall with (x := xs) in E;
    [|exact Hxs].
  apply Forall_forall. intros t Ht. apply forallb_forall with (x := t) in E;
    [|exact Ht].
  now apply Nat.ltb_lt.
Qed.

Definition bit_flips c p s :=
  flat_map
    (fun xs => match bit_bracket c p xs with None => [] | Some ys => ys end)
    (cached_rays s).

Lemma bit_flips_correct : forall c p s, s < 36 ->
  bit_flips c p s = flips (claim_board c) p s.
Proof.
  intros c p s H. rewrite <- fast_flips_correct by exact H.
  unfold bit_flips, fast_flips. pose proof (cached_rays_range s H) as Hxs.
  induction Hxs; simpl; [reflexivity|]. rewrite bit_bracket_correct by exact H0.
  now rewrite IHHxs.
Qed.

Fixpoint square_mask (xs : list nat) : N :=
  match xs with [] => 0%N
  | s :: rest => N.setbit (square_mask rest) (N.of_nat s)
  end.

Lemma square_mask_spec : forall xs t,
  N.testbit (square_mask xs) (N.of_nat t) = existsb (Nat.eqb t) xs.
Proof.
  induction xs as [|s rest IH]; intro t; simpl; [reflexivity|].
  rewrite N.setbit_eqb, IH.
  assert (E : (N.of_nat s =? N.of_nat t)%N = (t =? s)).
  { destruct (Nat.eqb_spec t s) as [H|H].
    - subst. apply N.eqb_refl.
    - apply N.eqb_neq. intro K. apply H. symmetry. now apply Nat2N.inj. }
  rewrite E. reflexivity.
Qed.

Definition bit_update (c : claim) (p : player) (s : nat)
    (captured : list nat) : claim :=
  let mask := square_mask (s :: captured) in
  match p with
  | Black =>
    Claim (N.lor (black_bits c) mask) (N.ldiff (white_bits c) mask) White
  | White =>
    Claim (N.ldiff (black_bits c) mask) (N.lor (white_bits c) mask) Black
  end.

Lemma bit_update_correct : forall c p s captured,
  claim_board (bit_update c p s captured) =
    put_and_flip (claim_board c) p s captured.
Proof.
  intros c p s captured. unfold put_and_flip.
  unfold claim_board at 1. apply map_ext_in. intros t Ht.
  assert (Ht36 : t < 36) by (apply in_seq in Ht; lia).
  rewrite <- bit_cell_correct by exact Ht36.
  unfold bit_update, bit_cell; rewrite !testbit_nat_correct; destruct p;
    cbn [black_bits white_bits];
    rewrite !N.lor_spec, !N.ldiff_spec, !square_mask_spec; simpl;
    destruct (Nat.eqb t s), (existsb (Nat.eqb t) captured),
             (N.testbit (black_bits c) (N.of_nat t)), (N.testbit (white_bits c)
               (N.of_nat t)); reflexivity.
Qed.

Definition bit_play (c : claim) (p : player) (s : nat) : option claim :=
  if s <? 36 then
    match bit_cell c s with
    | Stone _ => None
    | Empty =>
        match bit_flips c p s with [] => None
        | captured => Some (bit_update c p s captured)
        end
    end
  else None.

Lemma bit_play_correct : forall c p s,
  option_map claim_board (bit_play c p s) = play (claim_board c) p s.
Proof.
  intros c p s. unfold bit_play, play. destruct (s <? 36) eqn:Hs;
    [|reflexivity].
  apply Nat.ltb_lt in Hs.
  rewrite bit_cell_correct, bit_flips_correct by exact Hs.
  destruct (cell_at (claim_board c) s); [|reflexivity].
  destruct (flips (claim_board c) p s); [reflexivity|].
  simpl. now rewrite bit_update_correct.
Qed.

Definition full_bit_moves (c : claim) (p : player) : list (nat * claim) :=
  flat_map
    (fun s => match bit_play c p s with None => []
              | Some c' => [(s, c')]
              end)
    squares.

Lemma full_bit_moves_correct : forall c p,
  map (fun sc => (fst sc, claim_board (snd sc))) (full_bit_moves c p) =
    moves (claim_board c) p.
Proof.
  intros c p. unfold full_bit_moves, moves. generalize squares.
  intro xs. induction xs as [|s xs IH]; simpl; [reflexivity|].
  rewrite map_app, IH. pose proof (bit_play_correct c p s) as E.
  destruct (bit_play c p s) as [c'|]; simpl in E; rewrite <- E; reflexivity.
Qed.

Lemma fast_board_bit_cells : forall c,
  fast_claim_board c = map (bit_cell c) squares.
Proof.
  intro c. rewrite fast_claim_board_correct. unfold claim_board.
  apply map_ext. intro i. unfold bit_cell. now rewrite !testbit_nat_correct.
Qed.

Definition bit_moves (c : claim) (p : player) : list (nat * claim) :=
  flat_map
    (fun sc => match snd sc with
               | Empty =>
                   match bit_play c p (fst sc) with None => []
                   | Some c' => [(fst sc, c')]
                   end
               | Stone _ => []
               end)
    (combine squares (fast_claim_board c)).

Lemma sparse_bit_moves_correct : forall c p, bit_moves c p = full_bit_moves c p.
Proof.
  intros c p. unfold bit_moves, full_bit_moves. rewrite fast_board_bit_cells.
  generalize squares. intro xs. induction xs as [|s xs IH]; simpl;
    [reflexivity|].
  rewrite IH. f_equal. unfold bit_play.
  destruct (s <? 36), (bit_cell c s); reflexivity.
Qed.

Lemma bit_moves_correct : forall c p,
  map (fun sc =>
    (fst sc, claim_board (snd sc))) (bit_moves c p) = moves (claim_board c) p.
Proof.
  intros. rewrite sparse_bit_moves_correct. apply full_bit_moves_correct.
Qed.

Definition bit_no_moveb c p :=
  match bit_moves c p with [] => true | _ => false end.

Lemma bit_no_moveb_correct : forall c p, bit_no_moveb c p = no_moveb
  (claim_board c) p.
Proof.
  intros c p. unfold bit_no_moveb, no_moveb. rewrite <- bit_moves_correct.
  destruct (bit_moves c p); reflexivity.
Qed.
Print Assumptions bit_play_correct.
