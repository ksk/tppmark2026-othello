From Stdlib Require Import List Bool Arith Lia ZArith.
From TPP2026.Six Require Import Rules Bounds Dag.
Import ListNotations.

(** Geometry is fixed, so compute it once. No property of a game is assumed. *)

Definition cached_rays (s : nat) : list (list nat) :=
  match s with
  | 0 =>
      [[]; []; [1; 2; 3; 4; 5]; [7; 14; 21; 28; 35]; [6; 12; 18; 24; 30]; [];
       []; []]
  | 1 =>
      [[]; []; [2; 3; 4; 5]; [8; 15; 22; 29]; [7; 13; 19; 25; 31]; [6]; [0]; []]
  | 2 =>
      [[]; []; [3; 4; 5]; [9; 16; 23]; [8; 14; 20; 26; 32]; [7; 12]; [1; 0]; []]
  | 3 =>
      [[]; []; [4; 5]; [10; 17]; [9; 15; 21; 27; 33]; [8; 13; 18]; [2; 1; 0];
       []]
  | 4 =>
      [[]; []; [5]; [11]; [10; 16; 22; 28; 34]; [9; 14; 19; 24]; [3; 2; 1; 0];
       []]
  | 5 =>
      [[]; []; []; []; [11; 17; 23; 29; 35]; [10; 15; 20; 25; 30];
       [4; 3; 2; 1; 0]; []]
  | 6 =>
      [[0]; [1]; [7; 8; 9; 10; 11]; [13; 20; 27; 34]; [12; 18; 24; 30]; []; [];
       []]
  | 7 =>
      [[1]; [2]; [8; 9; 10; 11]; [14; 21; 28; 35]; [13; 19; 25; 31]; [12]; [6];
       [0]]
  | 8 =>
      [[2]; [3]; [9; 10; 11]; [15; 22; 29]; [14; 20; 26; 32]; [13; 18]; [7; 6];
       [1]]
  | 9 =>
      [[3]; [4]; [10; 11]; [16; 23]; [15; 21; 27; 33]; [14; 19; 24]; [8; 7; 6];
       [2]]
  | 10 =>
      [[4]; [5]; [11]; [17]; [16; 22; 28; 34]; [15; 20; 25; 30]; [9; 8; 7; 6];
       [3]]
  | 11 =>
      [[5]; []; []; []; [17; 23; 29; 35]; [16; 21; 26; 31]; [10; 9; 8; 7; 6];
       [4]]
  | 12 =>
      [[6; 0]; [7; 2]; [13; 14; 15; 16; 17]; [19; 26; 33]; [18; 24; 30]; []; [];
       []]
  | 13 =>
      [[7; 1]; [8; 3]; [14; 15; 16; 17]; [20; 27; 34]; [19; 25; 31]; [18]; [12];
       [6]]
  | 14 =>
      [[8; 2]; [9; 4]; [15; 16; 17]; [21; 28; 35]; [20; 26; 32]; [19; 24];
       [13; 12]; [7; 0]]
  | 15 =>
      [[9; 3]; [10; 5]; [16; 17]; [22; 29]; [21; 27; 33]; [20; 25; 30];
       [14; 13; 12]; [8; 1]]
  | 16 =>
      [[10; 4]; [11]; [17]; [23]; [22; 28; 34]; [21; 26; 31]; [15; 14; 13; 12];
       [9; 2]]
  | 17 =>
      [[11; 5]; []; []; []; [23; 29; 35]; [22; 27; 32]; [16; 15; 14; 13; 12];
       [10; 3]]
  | 18 =>
      [[12; 6; 0]; [13; 8; 3]; [19; 20; 21; 22; 23]; [25; 32]; [24; 30]; []; [];
       []]
  | 19 =>
      [[13; 7; 1]; [14; 9; 4]; [20; 21; 22; 23]; [26; 33]; [25; 31]; [24]; [18];
       [12]]
  | 20 =>
      [[14; 8; 2]; [15; 10; 5]; [21; 22; 23]; [27; 34]; [26; 32]; [25; 30];
       [19; 18]; [13; 6]]
  | 21 =>
      [[15; 9; 3]; [16; 11]; [22; 23]; [28; 35]; [27; 33]; [26; 31];
       [20; 19; 18]; [14; 7; 0]]
  | 22 =>
      [[16; 10; 4]; [17]; [23]; [29]; [28; 34]; [27; 32]; [21; 20; 19; 18];
       [15; 8; 1]]
  | 23 =>
      [[17; 11; 5]; []; []; []; [29; 35]; [28; 33]; [22; 21; 20; 19; 18];
       [16; 9; 2]]
  | 24 =>
      [[18; 12; 6; 0]; [19; 14; 9; 4]; [25; 26; 27; 28; 29]; [31]; [30]; []; [];
       []]
  | 25 =>
      [[19; 13; 7; 1]; [20; 15; 10; 5]; [26; 27; 28; 29]; [32]; [31]; [30];
       [24]; [18]]
  | 26 =>
      [[20; 14; 8; 2]; [21; 16; 11]; [27; 28; 29]; [33]; [32]; [31]; [25; 24];
       [19; 12]]
  | 27 =>
      [[21; 15; 9; 3]; [22; 17]; [28; 29]; [34]; [33]; [32]; [26; 25; 24];
       [20; 13; 6]]
  | 28 =>
      [[22; 16; 10; 4]; [23]; [29]; [35]; [34]; [33]; [27; 26; 25; 24];
       [21; 14; 7; 0]]
  | 29 =>
      [[23; 17; 11; 5]; []; []; []; [35]; [34]; [28; 27; 26; 25; 24];
       [22; 15; 8; 1]]
  | 30 =>
      [[24; 18; 12; 6; 0]; [25; 20; 15; 10; 5]; [31; 32; 33; 34; 35]; []; [];
       []; []; []]
  | 31 =>
      [[25; 19; 13; 7; 1]; [26; 21; 16; 11]; [32; 33; 34; 35]; []; []; []; [30];
       [24]]
  | 32 =>
      [[26; 20; 14; 8; 2]; [27; 22; 17]; [33; 34; 35]; []; []; []; [31; 30];
       [25; 18]]
  | 33 =>
      [[27; 21; 15; 9; 3]; [28; 23]; [34; 35]; []; []; []; [32; 31; 30];
       [26; 19; 12]]
  | 34 =>
      [[28; 22; 16; 10; 4]; [29]; [35]; []; []; []; [33; 32; 31; 30];
       [27; 20; 13; 6]]
  | 35 =>
      [[29; 23; 17; 11; 5]; []; []; []; []; []; [34; 33; 32; 31; 30];
       [28; 21; 14; 7; 0]]
  | _ => []
  end.

Lemma cached_rays_correct : forall s, s < 36 ->
  cached_rays s = map (ray 5 s) directions.
Proof.
  intros s H. do 36 (destruct s as [|s]; [reflexivity|]). lia.
Qed.

Definition fast_flips (b : board) (p : player) (s : nat) : list nat :=
  flat_map
    (fun xs => match bracket b p xs with None => [] | Some ys => ys end)
    (cached_rays s).

Lemma fast_flips_correct : forall b p s, s < 36 ->
  fast_flips b p s = flips b p s.
Proof.
  intros b p s H. unfold fast_flips, flips, captured_in.
  rewrite cached_rays_correct by exact H. reflexivity.
Qed.

Definition fast_play (b : board) (p : player) (s : nat) : option board :=
  if s <? 36 then
    match cell_at b s with
    | Stone _ => None
    | Empty =>
        match fast_flips b p s with
        | [] => None
        | captured => Some (put_and_flip b p s captured)
        end
    end
  else None.

Lemma fast_play_correct : forall b p s, fast_play b p s = play b p s.
Proof.
  intros b p s. unfold fast_play, play. destruct (s <? 36) eqn:Hs;
    [|reflexivity].
  apply Nat.ltb_lt in Hs. rewrite fast_flips_correct by exact Hs. reflexivity.
Qed.

Definition fast_moves (b : board) (p : player) : list (nat * board) :=
  flat_map
    (fun s => match fast_play b p s with Some b' => [(s, b')]
              | None => []
              end)
    squares.

Lemma fast_moves_correct : forall b p, fast_moves b p = moves b p.
Proof.
  intros b p. unfold fast_moves, moves. apply flat_map_ext. intro s.
  rewrite fast_play_correct. reflexivity.
Qed.

Definition fast_no_moveb (b : board) (p : player) : bool :=
  match fast_moves b p with [] => true | _ => false end.

Lemma fast_no_moveb_correct : forall b p, fast_no_moveb b p = no_moveb b p.
Proof.
  intros b p. unfold fast_no_moveb, no_moveb. now rewrite fast_moves_correct.
Qed.

(** Store decoded boards in the environment: references do not decode them
  again. *)

Definition decoded_claim := (board * player)%type.

Definition decoded_valid who goal (c : decoded_claim) :=
  forces who goal (fst c) (snd c).

Definition decoded_reference (env : trie decoded_claim) (b : board) (p : player)
    (id : positive) :=
  match lookup id env with None => false
  | Some c => board_eqb b (fst c) && same_player p (snd c)
  end.

Lemma decoded_reference_sound : forall who goal env,
  trie_all (decoded_valid who goal) env -> forall b p id,
  decoded_reference env b p id = true -> forces who goal b p.
Proof.
  intros who goal env Henv b p id H. unfold decoded_reference in H.
  destruct (lookup id env) as [[c q]|] eqn:E; [|discriminate].
  apply andb_true_iff in H as [Hb Hp]. apply board_eqb_sound in Hb.
  apply same_player_true in Hp. simpl in *. subst b p.
  exact (lookup_all decoded_claim (decoded_valid who goal) env Henv id (c, q)
    E).
Qed.

Definition fast_node who goalb (env : trie decoded_claim) (b : board) p
    (op : instruction) : bool :=
  match op with
  | DEnd => fast_no_moveb b Black && fast_no_moveb b White && goalb b
  | DChoose square child =>
      if same_player p who then
        match fast_play b who square with
        | None => false
        | Some b' => decoded_reference env b' (other who) child
        end
      else false
  | DAll children =>
      if same_player p (other who) then
        match fast_moves b (other who) with
        | [] => false
        | ms =>
            check_all (fun mb child => decoded_reference env (snd mb) who child)
              ms children
        end
      else false
  | DPass child =>
      fast_no_moveb b p && negb (fast_no_moveb b (other p)) &&
      decoded_reference env b (other p) child
  end.

Lemma fast_node_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall env b p op,
  trie_all (decoded_valid who goal) env ->
    fast_node who goalb env b p op = true -> forces who goal b p.
Proof.
  intros who goalb goal Hgoal env b p op Henv H.
  destruct op as [|s child|children|child]; cbn [fast_node] in H;
    repeat rewrite fast_no_moveb_correct in H;
      try rewrite fast_play_correct in H;
    try rewrite fast_moves_correct in H.
  - apply andb_true_iff in H as [Hmoves Hscore].
    apply andb_true_iff in Hmoves as [Hb Hw].
    apply force_end; [split; apply no_moveb_spec; assumption|auto].
  - destruct (same_player p who) eqn:Hp; [|discriminate].
    apply same_player_true in Hp. subst p.
    destruct (play b who s) as [b'|] eqn:Hplay; [|discriminate].
    eapply force_choose.
    + split; [eapply play_in_range; eauto|exact Hplay].
    + eapply decoded_reference_sound; eauto.
  - destruct (same_player p (other who)) eqn:Hp; [|discriminate].
    apply same_player_true in Hp. subst p.
    destruct (moves b (other who)) as [|[s b'] rest] eqn:Hmoves;
      [discriminate|].
    apply force_all.
    + exists s, b'. apply moves_spec. rewrite Hmoves. simpl. auto.
    + intros t b'' Hlegal. apply moves_spec in Hlegal. rewrite Hmoves in Hlegal.
      destruct (check_all_member _ _ _ _ _ H (t, b'') Hlegal) as [child Hchild].
      eapply decoded_reference_sound; eauto.
  - apply andb_true_iff in H as [Hpass Hchild].
    apply andb_true_iff in Hpass as [Hnone Hsome].
    apply force_pass.
    + apply no_moveb_spec. exact Hnone.
    + apply has_moveb_spec. exact Hsome.
    + eapply decoded_reference_sound; eauto.
Qed.

Fixpoint fast_run who goalb entries
    (env : trie decoded_claim) : option (trie decoded_claim) :=
  match entries with
  | [] => Some env
  | e :: rest =>
      let c := entry_claim e in
      let b := claim_board c in
      if fast_node who goalb env b (claim_turn c) (entry_op e)
      then fast_run who goalb rest (insert (entry_id e) (b, claim_turn c) env)
      else None
  end.

Lemma fast_run_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall entries env result,
  trie_all (decoded_valid who goal) env ->
    fast_run who goalb entries env = Some result ->
  trie_all (decoded_valid who goal) result.
Proof.
  intros who goalb goal Hgoal entries. induction entries as [|e rest IH];
    intros env result Henv H.
  - simpl in H. inversion H; subst. exact Henv.
  - simpl in H. destruct (fast_node _ _ _ _ _ _) eqn:E; [|discriminate].
    eapply IH; [|exact H]. apply insert_all; [exact Henv|].
    unfold decoded_valid. simpl. eapply fast_node_sound; eauto.
Qed.

Definition fast_verify who goalb entries root b p :=
  match fast_run who goalb entries Tip with
  | None => false
  | Some env => decoded_reference env b p root
  end.

Theorem fast_verify_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall entries root b p,
  fast_verify who goalb entries root b p = true -> forces who goal b p.
Proof.
  intros who goalb goal Hgoal entries root b p H. unfold fast_verify in H.
  destruct (fast_run who goalb entries Tip) as [env|] eqn:E; [|discriminate].
  eapply decoded_reference_sound; [|exact H]. eapply fast_run_sound; eauto.
  exact I.
Qed.
Print Assumptions fast_verify_sound.
