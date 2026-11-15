From Stdlib Require Import List Bool Arith Lia NArith.
From TPP2026.Six Require Import Rules Bounds Dag FastDag FastDecode BitRules.
Import ListNotations.

Record grid :=
  Grid {
    g00 : cell; g01 : cell; g02 : cell; g03 : cell; g04 : cell; g05 : cell;
    g06 : cell; g07 : cell; g08 : cell; g09 : cell; g10 : cell; g11 : cell;
    g12 : cell; g13 : cell; g14 : cell; g15 : cell; g16 : cell; g17 : cell;
    g18 : cell; g19 : cell; g20 : cell; g21 : cell; g22 : cell; g23 : cell;
    g24 : cell; g25 : cell; g26 : cell; g27 : cell; g28 : cell; g29 : cell;
    g30 : cell; g31 : cell; g32 : cell; g33 : cell; g34 : cell; g35 : cell
  }.

Definition grid_list g : board :=
  [g00 g; g01 g; g02 g; g03 g; g04 g; g05 g;
   g06 g; g07 g; g08 g; g09 g; g10 g; g11 g;
   g12 g; g13 g; g14 g; g15 g; g16 g; g17 g;
   g18 g; g19 g; g20 g; g21 g; g22 g; g23 g;
   g24 g; g25 g; g26 g; g27 g; g28 g; g29 g;
   g30 g; g31 g; g32 g; g33 g; g34 g; g35 g].

Definition grid_of_list (b : board) : grid :=
  match b with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 ::
    a6 :: a7 :: a8 :: a9 :: a10 :: a11 ::
    a12 :: a13 :: a14 :: a15 :: a16 :: a17 ::
    a18 :: a19 :: a20 :: a21 :: a22 :: a23 ::
    a24 :: a25 :: a26 :: a27 :: a28 :: a29 ::
    a30 :: a31 :: a32 :: a33 :: a34 :: a35 :: rest =>
      Grid a0 a1 a2 a3 a4 a5
        a6 a7 a8 a9 a10 a11
        a12 a13 a14 a15 a16 a17
        a18 a19 a20 a21 a22 a23
        a24 a25 a26 a27 a28 a29
        a30 a31 a32 a33 a34 a35
  | _ =>
      Grid Empty Empty Empty Empty Empty Empty
        Empty Empty Empty Empty Empty Empty
        Empty Empty Empty Empty Empty Empty
        Empty Empty Empty Empty Empty Empty
        Empty Empty Empty Empty Empty Empty
        Empty Empty Empty Empty Empty Empty
  end.

Lemma grid_list_correct : forall b, well_formed b ->
  grid_list (grid_of_list b) = b.
Proof.
  intros b H. unfold well_formed in H.
  do 36 (let a := fresh "a" in destruct b as [|a b]; [simpl in H; lia|]).
  destruct b; [reflexivity|simpl in H; lia].
Qed.

Definition selector s : grid -> cell :=
  match s with
  | 0 => g00
  | 1 => g01
  | 2 => g02
  | 3 => g03
  | 4 => g04
  | 5 => g05
  | 6 => g06
  | 7 => g07
  | 8 => g08
  | 9 => g09
  | 10 => g10
  | 11 => g11
  | 12 => g12
  | 13 => g13
  | 14 => g14
  | 15 => g15
  | 16 => g16
  | 17 => g17
  | 18 => g18
  | 19 => g19
  | 20 => g20
  | 21 => g21
  | 22 => g22
  | 23 => g23
  | 24 => g24
  | 25 => g25
  | 26 => g26
  | 27 => g27
  | 28 => g28
  | 29 => g29
  | 30 => g30
  | 31 => g31
  | 32 => g32
  | 33 => g33
  | 34 => g34
  | 35 => g35
  | _ => fun _ => Empty
  end.

Lemma selector_correct : forall g s, s < 36 ->
  selector s g = cell_at (grid_list g) s.
Proof. intros g s H. do 36 (destruct s as [|s]; [reflexivity|]). lia. Qed.

Definition grid_rays s : list (list (nat * (grid -> cell))) :=
  match s with
  | 0 =>
      [[]; []; [(1, g01); (2, g02); (3, g03); (4, g04); (5, g05)];
       [(7, g07); (14, g14); (21, g21); (28, g28); (35, g35)];
       [(6, g06); (12, g12); (18, g18); (24, g24); (30, g30)]; []; []; []]
  | 1 =>
      [[]; []; [(2, g02); (3, g03); (4, g04); (5, g05)];
       [(8, g08); (15, g15); (22, g22); (29, g29)];
       [(7, g07); (13, g13); (19, g19); (25, g25); (31, g31)]; [(6, g06)];
       [(0, g00)]; []]
  | 2 =>
      [[]; []; [(3, g03); (4, g04); (5, g05)]; [(9, g09); (16, g16); (23, g23)];
       [(8, g08); (14, g14); (20, g20); (26, g26); (32, g32)];
       [(7, g07); (12, g12)]; [(1, g01); (0, g00)]; []]
  | 3 =>
      [[]; []; [(4, g04); (5, g05)]; [(10, g10); (17, g17)];
       [(9, g09); (15, g15); (21, g21); (27, g27); (33, g33)];
       [(8, g08); (13, g13); (18, g18)]; [(2, g02); (1, g01); (0, g00)]; []]
  | 4 =>
      [[]; []; [(5, g05)]; [(11, g11)];
       [(10, g10); (16, g16); (22, g22); (28, g28); (34, g34)];
       [(9, g09); (14, g14); (19, g19); (24, g24)];
       [(3, g03); (2, g02); (1, g01); (0, g00)]; []]
  | 5 =>
      [[]; []; []; []; [(11, g11); (17, g17); (23, g23); (29, g29); (35, g35)];
       [(10, g10); (15, g15); (20, g20); (25, g25); (30, g30)];
       [(4, g04); (3, g03); (2, g02); (1, g01); (0, g00)]; []]
  | 6 =>
      [[(0, g00)]; [(1, g01)];
       [(7, g07); (8, g08); (9, g09); (10, g10); (11, g11)];
       [(13, g13); (20, g20); (27, g27); (34, g34)];
       [(12, g12); (18, g18); (24, g24); (30, g30)]; []; []; []]
  | 7 =>
      [[(1, g01)]; [(2, g02)]; [(8, g08); (9, g09); (10, g10); (11, g11)];
       [(14, g14); (21, g21); (28, g28); (35, g35)];
       [(13, g13); (19, g19); (25, g25); (31, g31)]; [(12, g12)]; [(6, g06)];
       [(0, g00)]]
  | 8 =>
      [[(2, g02)]; [(3, g03)]; [(9, g09); (10, g10); (11, g11)];
       [(15, g15); (22, g22); (29, g29)];
       [(14, g14); (20, g20); (26, g26); (32, g32)]; [(13, g13); (18, g18)];
       [(7, g07); (6, g06)]; [(1, g01)]]
  | 9 =>
      [[(3, g03)]; [(4, g04)]; [(10, g10); (11, g11)]; [(16, g16); (23, g23)];
       [(15, g15); (21, g21); (27, g27); (33, g33)];
       [(14, g14); (19, g19); (24, g24)]; [(8, g08); (7, g07); (6, g06)];
       [(2, g02)]]
  | 10 =>
      [[(4, g04)]; [(5, g05)]; [(11, g11)]; [(17, g17)];
       [(16, g16); (22, g22); (28, g28); (34, g34)];
       [(15, g15); (20, g20); (25, g25); (30, g30)];
       [(9, g09); (8, g08); (7, g07); (6, g06)]; [(3, g03)]]
  | 11 =>
      [[(5, g05)]; []; []; []; [(17, g17); (23, g23); (29, g29); (35, g35)];
       [(16, g16); (21, g21); (26, g26); (31, g31)];
       [(10, g10); (9, g09); (8, g08); (7, g07); (6, g06)]; [(4, g04)]]
  | 12 =>
      [[(6, g06); (0, g00)]; [(7, g07); (2, g02)];
       [(13, g13); (14, g14); (15, g15); (16, g16); (17, g17)];
       [(19, g19); (26, g26); (33, g33)]; [(18, g18); (24, g24); (30, g30)]; [];
       []; []]
  | 13 =>
      [[(7, g07); (1, g01)]; [(8, g08); (3, g03)];
       [(14, g14); (15, g15); (16, g16); (17, g17)];
       [(20, g20); (27, g27); (34, g34)]; [(19, g19); (25, g25); (31, g31)];
       [(18, g18)]; [(12, g12)]; [(6, g06)]]
  | 14 =>
      [[(8, g08); (2, g02)]; [(9, g09); (4, g04)];
       [(15, g15); (16, g16); (17, g17)]; [(21, g21); (28, g28); (35, g35)];
       [(20, g20); (26, g26); (32, g32)]; [(19, g19); (24, g24)];
       [(13, g13); (12, g12)]; [(7, g07); (0, g00)]]
  | 15 =>
      [[(9, g09); (3, g03)]; [(10, g10); (5, g05)]; [(16, g16); (17, g17)];
       [(22, g22); (29, g29)]; [(21, g21); (27, g27); (33, g33)];
       [(20, g20); (25, g25); (30, g30)]; [(14, g14); (13, g13); (12, g12)];
       [(8, g08); (1, g01)]]
  | 16 =>
      [[(10, g10); (4, g04)]; [(11, g11)]; [(17, g17)]; [(23, g23)];
       [(22, g22); (28, g28); (34, g34)]; [(21, g21); (26, g26); (31, g31)];
       [(15, g15); (14, g14); (13, g13); (12, g12)]; [(9, g09); (2, g02)]]
  | 17 =>
      [[(11, g11); (5, g05)]; []; []; []; [(23, g23); (29, g29); (35, g35)];
       [(22, g22); (27, g27); (32, g32)];
       [(16, g16); (15, g15); (14, g14); (13, g13); (12, g12)];
       [(10, g10); (3, g03)]]
  | 18 =>
      [[(12, g12); (6, g06); (0, g00)]; [(13, g13); (8, g08); (3, g03)];
       [(19, g19); (20, g20); (21, g21); (22, g22); (23, g23)];
       [(25, g25); (32, g32)]; [(24, g24); (30, g30)]; []; []; []]
  | 19 =>
      [[(13, g13); (7, g07); (1, g01)]; [(14, g14); (9, g09); (4, g04)];
       [(20, g20); (21, g21); (22, g22); (23, g23)]; [(26, g26); (33, g33)];
       [(25, g25); (31, g31)]; [(24, g24)]; [(18, g18)]; [(12, g12)]]
  | 20 =>
      [[(14, g14); (8, g08); (2, g02)]; [(15, g15); (10, g10); (5, g05)];
       [(21, g21); (22, g22); (23, g23)]; [(27, g27); (34, g34)];
       [(26, g26); (32, g32)]; [(25, g25); (30, g30)]; [(19, g19); (18, g18)];
       [(13, g13); (6, g06)]]
  | 21 =>
      [[(15, g15); (9, g09); (3, g03)]; [(16, g16); (11, g11)];
       [(22, g22); (23, g23)]; [(28, g28); (35, g35)]; [(27, g27); (33, g33)];
       [(26, g26); (31, g31)]; [(20, g20); (19, g19); (18, g18)];
       [(14, g14); (7, g07); (0, g00)]]
  | 22 =>
      [[(16, g16); (10, g10); (4, g04)]; [(17, g17)]; [(23, g23)]; [(29, g29)];
       [(28, g28); (34, g34)]; [(27, g27); (32, g32)];
       [(21, g21); (20, g20); (19, g19); (18, g18)];
       [(15, g15); (8, g08); (1, g01)]]
  | 23 =>
      [[(17, g17); (11, g11); (5, g05)]; []; []; []; [(29, g29); (35, g35)];
       [(28, g28); (33, g33)];
       [(22, g22); (21, g21); (20, g20); (19, g19); (18, g18)];
       [(16, g16); (9, g09); (2, g02)]]
  | 24 =>
      [[(18, g18); (12, g12); (6, g06); (0, g00)];
       [(19, g19); (14, g14); (9, g09); (4, g04)];
       [(25, g25); (26, g26); (27, g27); (28, g28); (29, g29)]; [(31, g31)];
       [(30, g30)]; []; []; []]
  | 25 =>
      [[(19, g19); (13, g13); (7, g07); (1, g01)];
       [(20, g20); (15, g15); (10, g10); (5, g05)];
       [(26, g26); (27, g27); (28, g28); (29, g29)]; [(32, g32)]; [(31, g31)];
       [(30, g30)]; [(24, g24)]; [(18, g18)]]
  | 26 =>
      [[(20, g20); (14, g14); (8, g08); (2, g02)];
       [(21, g21); (16, g16); (11, g11)]; [(27, g27); (28, g28); (29, g29)];
       [(33, g33)]; [(32, g32)]; [(31, g31)]; [(25, g25); (24, g24)];
       [(19, g19); (12, g12)]]
  | 27 =>
      [[(21, g21); (15, g15); (9, g09); (3, g03)]; [(22, g22); (17, g17)];
       [(28, g28); (29, g29)]; [(34, g34)]; [(33, g33)]; [(32, g32)];
       [(26, g26); (25, g25); (24, g24)]; [(20, g20); (13, g13); (6, g06)]]
  | 28 =>
      [[(22, g22); (16, g16); (10, g10); (4, g04)]; [(23, g23)]; [(29, g29)];
       [(35, g35)]; [(34, g34)]; [(33, g33)];
       [(27, g27); (26, g26); (25, g25); (24, g24)];
       [(21, g21); (14, g14); (7, g07); (0, g00)]]
  | 29 =>
      [[(23, g23); (17, g17); (11, g11); (5, g05)]; []; []; []; [(35, g35)];
       [(34, g34)]; [(28, g28); (27, g27); (26, g26); (25, g25); (24, g24)];
       [(22, g22); (15, g15); (8, g08); (1, g01)]]
  | 30 =>
      [[(24, g24); (18, g18); (12, g12); (6, g06); (0, g00)];
       [(25, g25); (20, g20); (15, g15); (10, g10); (5, g05)];
       [(31, g31); (32, g32); (33, g33); (34, g34); (35, g35)]; []; []; []; [];
       []]
  | 31 =>
      [[(25, g25); (19, g19); (13, g13); (7, g07); (1, g01)];
       [(26, g26); (21, g21); (16, g16); (11, g11)];
       [(32, g32); (33, g33); (34, g34); (35, g35)]; []; []; []; [(30, g30)];
       [(24, g24)]]
  | 32 =>
      [[(26, g26); (20, g20); (14, g14); (8, g08); (2, g02)];
       [(27, g27); (22, g22); (17, g17)]; [(33, g33); (34, g34); (35, g35)]; [];
       []; []; [(31, g31); (30, g30)]; [(25, g25); (18, g18)]]
  | 33 =>
      [[(27, g27); (21, g21); (15, g15); (9, g09); (3, g03)];
       [(28, g28); (23, g23)]; [(34, g34); (35, g35)]; []; []; [];
       [(32, g32); (31, g31); (30, g30)]; [(26, g26); (19, g19); (12, g12)]]
  | 34 =>
      [[(28, g28); (22, g22); (16, g16); (10, g10); (4, g04)]; [(29, g29)];
       [(35, g35)]; []; []; []; [(33, g33); (32, g32); (31, g31); (30, g30)];
       [(27, g27); (20, g20); (13, g13); (6, g06)]]
  | 35 =>
      [[(29, g29); (23, g23); (17, g17); (11, g11); (5, g05)]; []; []; []; [];
       []; [(34, g34); (33, g33); (32, g32); (31, g31); (30, g30)];
       [(28, g28); (21, g21); (14, g14); (7, g07); (0, g00)]]
  | _ => []
  end.

Lemma grid_rays_correct : forall s, s < 36 ->
  grid_rays s = map (map (fun t => (t, selector t))) (cached_rays s).
Proof. intros s H. do 36 (destruct s as [|s]; [reflexivity|]). lia. Qed.

Fixpoint grid_bracket (g : grid) p
    (xs : list (nat * (grid -> cell))) : option (list nat) :=
  match xs with
  | [] => None
  | (s, get) :: rest =>
      match get g with
      | Empty => None
      | Stone q =>
          if same_player p q then Some []
          else match grid_bracket g p rest with None => None
               | Some ys => Some (s :: ys)
               end
      end
  end.

Lemma grid_bracket_correct : forall g p xs, Forall (fun s => s < 36) xs ->
  grid_bracket g p (map (fun s =>
    (s, selector s)) xs) = bracket (grid_list g) p xs.
Proof.
  intros g p xs H. induction H; simpl; [reflexivity|].
  rewrite selector_correct by exact H. rewrite IHForall. reflexivity.
Qed.

Definition grid_flips g p s :=
  flat_map
    (fun xs => match grid_bracket g p xs with None => [] | Some ys => ys end)
    (grid_rays s).

Lemma grid_flips_correct : forall g p s, s < 36 ->
  grid_flips g p s = fast_flips (grid_list g) p s.
Proof.
  intros g p s H. unfold grid_flips, fast_flips.
  rewrite grid_rays_correct by exact H.
  pose proof (cached_rays_range s H) as Hr. induction Hr; simpl; [reflexivity|].
  rewrite grid_bracket_correct by exact H0. now rewrite IHHr.
Qed.

Lemma fast_claim_well_formed : forall c, well_formed (fast_claim_board c).
Proof.
  intro c. rewrite fast_claim_board_correct.
  unfold well_formed, claim_board, squares. now rewrite length_map, length_seq.
Qed.

Definition grid_claim c := grid_of_list (fast_claim_board c).

Lemma grid_claim_correct : forall c, grid_list (grid_claim c) = claim_board c.
Proof.
  intro c. unfold grid_claim.
  rewrite grid_list_correct by apply fast_claim_well_formed.
  apply fast_claim_board_correct.
Qed.

Definition grid_play_with c g p s :=
  if s <? 36 then
    match selector s g with
    | Stone _ => None
    | Empty =>
        match grid_flips g p s with [] => None
        | captured => Some (bit_update c p s captured)
        end
    end
  else None.

Lemma grid_play_with_correct : forall c p s,
  grid_play_with c (grid_claim c) p s = bit_play c p s.
Proof.
  intros c p s. unfold grid_play_with, bit_play. destruct (s <? 36) eqn:E;
    [|reflexivity].
  apply Nat.ltb_lt in E.
  rewrite selector_correct, grid_flips_correct by exact E.
  rewrite grid_claim_correct.
  rewrite bit_cell_correct, bit_flips_correct, fast_flips_correct by exact E.
  reflexivity.
Qed.

Definition grid_play c p s := grid_play_with c (grid_claim c) p s.

Lemma grid_play_correct : forall c p s, grid_play c p s = bit_play c p s.
Proof. apply grid_play_with_correct. Qed.

Definition grid_moves c p :=
  let g := grid_claim c in
  flat_map
    (fun sc => match snd sc with
               | Empty =>
                   match grid_play_with c g p (fst sc) with None => []
                   | Some d => [(fst sc, d)]
                   end
               | Stone _ => []
               end)
    (combine squares (fast_claim_board c)).

Lemma grid_moves_correct : forall c p, grid_moves c p = bit_moves c p.
Proof.
  intros c p. unfold grid_moves, bit_moves. apply flat_map_ext. intros [s v].
  simpl.
  rewrite grid_play_with_correct. reflexivity.
Qed.

Definition grid_no_moveb c p :=
  match grid_moves c p with [] => true | _ => false end.

Lemma grid_no_moveb_correct : forall c p, grid_no_moveb c p = bit_no_moveb c p.
Proof.
  intros. unfold grid_no_moveb, bit_no_moveb. now rewrite grid_moves_correct.
Qed.
Print Assumptions grid_play_correct.
Print Assumptions grid_moves_correct.
