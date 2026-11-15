From Stdlib Require Import List Bool Arith Lia ZArith Sorting.Permutation
  Lists.Finite.
From TPP2026.Six Require Import Rules Bounds.
Import ListNotations.

Lemma square_member : forall s, In s squares <-> s < 36.
Proof. intro s. unfold squares. rewrite in_seq. lia. Qed.

Lemma mapped_cell : forall f s, s < 36 -> cell_at (map f squares) s = f s.
Proof.
  intros f s H. unfold cell_at, squares.
  rewrite (nth_indep _ Empty (f 0)) by (rewrite length_map, length_seq;
    exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Definition rotate_square s := if s <? 36 then 35 - s else s.

Definition transpose_square s := if s <? 36 then 6 * (s mod 6) + s / 6 else s.

Definition rotate_direction d :=
  match d with
  | North => South | NorthEast => SouthWest | East => West
  | SouthEast => NorthWest | South => North | SouthWest => NorthEast
  | West => East | NorthWest => SouthEast end.

Definition transpose_direction d :=
  match d with
  | North => West | NorthEast => SouthWest | East => South
  | SouthEast => SouthEast | South => East | SouthWest => NorthEast
  | West => North | NorthWest => NorthWest end.

Lemma rotate_square_involution : forall s, rotate_square (rotate_square s) = s.
Proof.
  intro s. do 36 (destruct s as [|s]; [reflexivity|]).
  reflexivity.
Qed.

Lemma transpose_square_involution : forall s, transpose_square (transpose_square
  s) = s.
Proof.
  intro s. do 36 (destruct s as [|s]; [reflexivity|]).
  reflexivity.
Qed.

Lemma rotate_square_range : forall s, s < 36 -> rotate_square s < 36.
Proof. intros s H. do 36 (destruct s as [|s]; [cbv; lia|]). lia. Qed.

Lemma transpose_square_range : forall s, s < 36 -> transpose_square s < 36.
Proof. intros s H. do 36 (destruct s as [|s]; [cbv; lia|]). lia. Qed.

Lemma canonical_board : forall b, well_formed b -> map (cell_at b) squares = b.
Proof.
  intros b H. apply nth_ext with (d := Empty) (d' := Empty).
  - unfold well_formed in H. rewrite length_map. unfold squares.
    rewrite length_seq. symmetry; exact H.
  - intros i Hi. rewrite length_map in Hi. unfold squares in Hi.
    rewrite length_seq in Hi.
    change (cell_at (map (cell_at b) squares) i = cell_at b i).
    apply mapped_cell. exact Hi.
Qed.

Lemma ray_range : forall s d, s < 36 -> Forall (fun t => t < 36) (ray 5 s d).
Proof.
  intros s d H. do 36 (destruct s as [|s]; [destruct d; repeat constructor;
    lia|]). lia.
Qed.

Record symmetry :=
  Symmetry {
    square_sym : nat -> nat;
    direction_sym : direction -> direction;
    square_involution : forall s, square_sym (square_sym s) = s;
    square_range : forall s, s < 36 -> square_sym s < 36;
    direction_permutation :
      Permutation (map direction_sym directions) directions;
    ray_symmetry : forall s d, s < 36 ->
      ray 5 (square_sym s) (direction_sym d) = map square_sym (ray 5 s d)
  }.

Definition transform (S : symmetry) (b : board) : board :=
  map (fun s => cell_at b (square_sym S s)) squares.

Lemma transform_well_formed : forall S b, well_formed (transform S b).
Proof.
  intros. unfold well_formed, transform, squares.
  now rewrite length_map, length_seq.
Qed.

Lemma transform_cell : forall S b s, s < 36 ->
  cell_at (transform S b) s = cell_at b (square_sym S s).
Proof.
  intros S b s H. exact (mapped_cell (fun t => cell_at b (square_sym S t)) s H).
Qed.

Lemma transform_involution : forall S b, well_formed b ->
  transform S (transform S b) = b.
Proof.
  intros S b H. rewrite <- (canonical_board b H) at 2.
  unfold transform at 1. apply map_ext_in. intros s Hs.
  apply square_member in Hs.
  rewrite transform_cell by (apply square_range; exact Hs).
  now rewrite square_involution.
Qed.

Lemma bracket_symmetry : forall S b p xs, Forall (fun s => s < 36) xs ->
  bracket (transform S b) p (map (square_sym S) xs) =
  option_map (map (square_sym S)) (bracket b p xs).
Proof.
  intros S b p xs H. induction H; simpl; [reflexivity|].
  rewrite transform_cell by (apply square_range; exact H).
  rewrite square_involution. destruct (cell_at b x) as [|q]; [reflexivity|].
  destruct (same_player p q); [reflexivity|]. rewrite IHForall.
  destruct (bracket b p l); reflexivity.
Qed.

Lemma captured_symmetry : forall S b p s d, s < 36 ->
  captured_in (transform S b) p (square_sym S s) (direction_sym S d) =
  map (square_sym S) (captured_in b p s d).
Proof.
  intros S b p s d H. unfold captured_in. rewrite ray_symmetry by exact H.
  rewrite bracket_symmetry by (apply ray_range; exact H).
  destruct (bracket b p (ray 5 s d)); reflexivity.
Qed.

Lemma flat_map_compose {A B C} (f : B -> list C) (g : A -> B) xs :
  flat_map f (map g xs) = flat_map (fun x => f (g x)) xs.
Proof. induction xs; simpl; congruence. Qed.

Lemma map_flatten {A B C} (f : B -> C) (g : A -> list B) xs :
  map f (flat_map g xs) = flat_map (fun x => map f (g x)) xs.
Proof.
  induction xs; simpl; [reflexivity|]. rewrite map_app, IHxs. reflexivity.
Qed.

Lemma flips_symmetry : forall S b p s, s < 36 ->
  Permutation (flips (transform S b) p (square_sym S s)) (map (square_sym S)
    (flips b p s)).
Proof.
  intros S b p s H. unfold flips.
  transitivity (flat_map (captured_in (transform S b) p (square_sym S s)) (map
    (direction_sym S) directions)).
  - apply Permutation_flat_map. symmetry. apply direction_permutation.
  - rewrite flat_map_compose, map_flatten.
    replace (flat_map (fun x =>
      captured_in (transform S b) p (square_sym S s) (direction_sym S x))
      directions)
      with (flat_map (fun x =>
        map (square_sym S) (captured_in b p s x)) directions).
    + reflexivity.
    + apply flat_map_ext. intro d. symmetry. apply captured_symmetry. exact H.
Qed.

Lemma existsb_permutation {A} (f : A -> bool) xs ys :
  Permutation xs ys -> existsb f xs = existsb f ys.
Proof.
  intro H. induction H; simpl; try congruence.
  destruct (f x), (f y), (existsb f l); reflexivity.
Qed.

Lemma put_permutation : forall b p s xs ys, Permutation xs ys ->
  put_and_flip b p s xs = put_and_flip b p s ys.
Proof.
  intros b p s xs ys H. unfold put_and_flip. apply map_ext. intro t.
  now rewrite (existsb_permutation (Nat.eqb t) xs ys H).
Qed.

Lemma symmetry_eqb : forall S s t,
  (square_sym S t =? s) = (t =? square_sym S s).
Proof.
  intros S s t. apply eq_true_iff_eq. rewrite !Nat.eqb_eq. split; intro H.
  - rewrite <- (square_involution S t), H. reflexivity.
  - rewrite H. apply square_involution.
Qed.

Lemma symmetry_existsb : forall S xs t,
  existsb (Nat.eqb (square_sym S t)) xs = existsb (Nat.eqb t) (map (square_sym
    S) xs).
Proof.
  intros S xs. induction xs; intro t; simpl; [reflexivity|].
  rewrite symmetry_eqb, IHxs. reflexivity.
Qed.

Lemma put_symmetry : forall S b p s xs,
  transform S (put_and_flip b p s xs) =
  put_and_flip (transform S b) p (square_sym S s) (map (square_sym S) xs).
Proof.
  intros S b p s xs. unfold transform at 1. unfold put_and_flip.
  apply map_ext_in. intros t Ht. apply square_member in Ht.
  rewrite mapped_cell by (apply square_range; exact Ht).
  rewrite transform_cell by exact Ht. rewrite symmetry_eqb, symmetry_existsb.
  reflexivity.
Qed.

Definition capture_result b p s xs :=
  match xs with [] => None | x :: rest => Some (put_and_flip b p s (x ::
    rest)) end.

Lemma capture_result_perm : forall b p s xs ys, Permutation xs ys ->
  capture_result b p s xs = capture_result b p s ys.
Proof.
  intros b p s xs ys H. destruct xs, ys; try reflexivity;
    try (apply Permutation_length in H; simpl in H; discriminate).
  unfold capture_result. f_equal. apply put_permutation. exact H.
Qed.

Lemma play_symmetry : forall S b p s, s < 36 ->
  play (transform S b) p (square_sym S s) = option_map (transform S) (play b p
    s).
Proof.
  intros S b p s H. unfold play.
  assert (Hs : (s <? 36) = true) by now apply Nat.ltb_lt.
  assert (Ht : (square_sym S s <? 36) = true) by (apply Nat.ltb_lt;
    apply square_range; exact H).
  rewrite Hs, Ht, transform_cell by (apply square_range; exact H).
  rewrite square_involution. destruct (cell_at b s); [|reflexivity].
  change (capture_result (transform S b) p (square_sym S s) (flips (transform S
    b) p (square_sym S s)) =
    option_map (transform S) (capture_result b p s (flips b p s))).
  rewrite (capture_result_perm _ _ _ _ _ (flips_symmetry S b p s H)).
  destruct (flips b p s); simpl; [reflexivity|]. now rewrite put_symmetry.
Qed.

Lemma legal_symmetry : forall S b p s b', legal_move b p s b' ->
  legal_move (transform S b) p (square_sym S s) (transform S b').
Proof.
  intros S b p s b' [Hs Hp]. apply square_member in Hs. split.
  - apply square_member. apply square_range. exact Hs.
  - rewrite play_symmetry by exact Hs. now rewrite Hp.
Qed.

Lemma no_move_symmetry : forall S b p, well_formed b -> no_move b p ->
  no_move (transform S b) p.
Proof.
  intros S b p Hwf Hnone t c Hlegal.
  pose proof (legal_symmetry S _ _ _ _ Hlegal) as Hback.
  rewrite transform_involution in Hback by exact Hwf. eapply Hnone. exact Hback.
Qed.

Lemma has_move_symmetry : forall S b p, has_move b p ->
  has_move (transform S b) p.
Proof.
  intros S b p [s [c H]]. exists (square_sym S s), (transform S c).
  now apply legal_symmetry.
Qed.

Theorem forces_symmetry : forall S who goal,
  (forall b, well_formed b -> goal b -> goal (transform S b)) ->
  forall b p, forces who goal b p -> well_formed b ->
    forces who goal (transform S b) p.
Proof.
  intros S who goal Hgoal b p H. induction H; intro Hwf.
  - apply force_end.
    + destruct H as [Hb Hw]. split; apply no_move_symmetry; assumption.
    + apply Hgoal; assumption.
  - eapply force_choose; [apply legal_symmetry; exact H|].
    apply IHforces. eapply play_well_formed. exact (proj2 H).
  - apply force_all; [apply has_move_symmetry; exact H|].
    intros s c Hlegal. pose proof (legal_symmetry S _ _ _ _ Hlegal) as Hback.
    rewrite transform_involution in Hback by exact Hwf.
    specialize (H1 _ _ Hback (transform_well_formed S c)).
    rewrite transform_involution in H1 by (eapply play_well_formed;
      exact (proj2 Hlegal)). exact H1.
  - apply force_pass.
    + apply no_move_symmetry; assumption.
    + apply has_move_symmetry; assumption.
    + apply IHforces. exact Hwf.
Qed.

Definition rotation : symmetry.
Proof.
  refine (Symmetry rotate_square rotate_direction rotate_square_involution
    rotate_square_range _ _).
  - apply NoDup_Permutation.
    + cbn. repeat constructor; simpl; intuition discriminate.
    + cbn. repeat constructor; simpl; intuition discriminate.
    + intro d. destruct d; cbn; intuition.
  - intros s d H. do 36 (destruct s as [|s]; [destruct d; reflexivity|]). lia.
Defined.

Definition transposition : symmetry.
Proof.
  refine (Symmetry transpose_square transpose_direction
    transpose_square_involution transpose_square_range _ _).
  - apply NoDup_Permutation.
    + cbn. repeat constructor; simpl; intuition discriminate.
    + cbn. repeat constructor; simpl; intuition discriminate.
    + intro d. destruct d; cbn; intuition.
  - intros s d H. do 36 (destruct s as [|s]; [destruct d; reflexivity|]). lia.
Defined.

Lemma square_sym_injective : forall S x y, square_sym S x = square_sym S y ->
  x = y.
Proof.
  intros S x y H.
  rewrite <- (square_involution S x), <- (square_involution S y). now rewrite H.
Qed.

Lemma square_sym_permutation : forall S, Permutation (map (square_sym S)
  squares) squares.
Proof.
  intro S. apply NoDup_Permutation.
  - apply Injective_map_NoDup; [exact (square_sym_injective S)|].
    apply seq_NoDup.
  - apply seq_NoDup.
  - intro x. rewrite in_map_iff. split.
    + intros [y [ <- Hy]]. apply square_member, square_range, square_member.
      exact Hy.
    + intro Hx. exists (square_sym S x). split; [apply square_involution|].
      apply square_member, square_range, square_member. exact Hx.
Qed.

Lemma transform_permutation : forall S b, well_formed b ->
  Permutation (transform S b) b.
Proof.
  intros S b H. rewrite <- (canonical_board b H) at 2. unfold transform.
  rewrite <- map_map. apply Permutation_map. apply square_sym_permutation.
Qed.

Lemma filter_length_permutation : forall A (f : A -> bool) xs ys,
  Permutation xs ys -> length (filter f xs) = length (filter f ys).
Proof.
  intros A f xs ys H. induction H; simpl; try congruence.
  - destruct (f x); simpl; congruence.
  - destruct (f x), (f y); simpl; reflexivity.
Qed.

Lemma symmetry_score : forall S b, well_formed b ->
  black_score (transform S b) = black_score b.
Proof.
  intros S b H. unfold black_score, count.
  rewrite ! (filter_length_permutation _ _ _ _ (transform_permutation S b H)).
  reflexivity.
Qed.

Corollary upper_bound_symmetry : forall S b p z, well_formed b ->
  upper_bound b p z -> upper_bound (transform S b) p z.
Proof.
  intros S b p z Hwf H. unfold upper_bound in *. eapply forces_symmetry;
    [|exact H|exact Hwf].
  intros c Hc Hscore. now rewrite symmetry_score by exact Hc.
Qed.

Corollary lower_bound_symmetry : forall S b p z, well_formed b ->
  lower_bound b p z -> lower_bound (transform S b) p z.
Proof.
  intros S b p z Hwf H. unfold lower_bound in *. eapply forces_symmetry;
    [|exact H|exact Hwf].
  intros c Hc Hscore. now rewrite symmetry_score by exact Hc.
Qed.
Print Assumptions upper_bound_symmetry.
Print Assumptions lower_bound_symmetry.
