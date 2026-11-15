From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

(** Concrete definitions used by the 6x6 certificates.
    boards/Six.v instantiates the common rules with these types.
    proofs/equivalence/Six.v proves agreement for arbitrary boards. *)

(** The 6 x 6 board uses row-major square numbers 0,...,35.
    a1 = 0, f1 = 5, a6 = 30, f6 = 35.  Black moves first. *)

Inductive player := Black | White.

Inductive cell := Empty | Stone (p : player).

Definition board := list cell.

Definition other (p : player) : player :=
  match p with Black => White | White => Black end.

Definition same_player (p q : player) : bool :=
  match p, q with Black, Black | White, White => true | _, _ => false end.

Definition squares : list nat := seq 0 36.

Definition well_formed (b : board) : Prop := length b = 36.

Definition cell_at (b : board) (s : nat) : cell := nth s b Empty.

Inductive direction :=
  North | NorthEast | East | SouthEast | South | SouthWest | West | NorthWest.

Definition directions :=
  [North; NorthEast; East; SouthEast; South; SouthWest; West; NorthWest].

(** One geometric step, with explicit row/column boundary checks. *)

Definition step (s : nat) (d : direction) : option nat :=
  if s <? 36 then
    let r := s / 6 in
    let c := s mod 6 in
    match d with
    | North => if 0 <? r then Some (s - 6) else None
    | NorthEast => if (0 <? r) && (c <? 5) then Some (s - 5) else None
    | East => if c <? 5 then Some (s + 1) else None
    | SouthEast => if (r <? 5) && (c <? 5) then Some (s + 7) else None
    | South => if r <? 5 then Some (s + 6) else None
    | SouthWest => if (r <? 5) && (0 <? c) then Some (s + 5) else None
    | West => if 0 <? c then Some (s - 1) else None
    | NorthWest => if (0 <? r) && (0 <? c) then Some (s - 7) else None
    end
  else None.

Fixpoint ray (fuel s : nat) (d : direction) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match step s d with
      | None => []
      | Some t => t :: ray fuel' t d
      end
  end.

(** On this board every geometric ray is exhausted after five squares.
    This is independent of the contents of the board. *)

Lemma ray_five_sufficient : forall s d,
  s < 36 -> ray 6 s d = ray 5 s d.
Proof.
  intros s d H.
  do 36 (destruct s as [|s]; [destruct d; reflexivity |]).
  lia.
Qed.

(** A nonempty sequence of opponent stones is captured exactly when
    followed by a friendly stone.  None means no friendly endpoint;
    Some [] means that the first square already has a friendly stone. *)

Fixpoint bracket (b : board) (p : player) (xs : list nat) : option (list nat) :=
  match xs with
  | [] => None
  | s :: rest =>
      match cell_at b s with
      | Empty => None
      | Stone q =>
          if same_player p q then Some []
          else match bracket b p rest with
               | None => None
               | Some captured => Some (s :: captured)
               end
      end
  end.

Definition captured_in (b : board) (p : player) (s : nat)
    (d : direction) : list nat :=
  match bracket b p (ray 5 s d) with
  | None => []
  | Some xs => xs
  end.

Definition flips (b : board) (p : player) (s : nat) : list nat :=
  flat_map (captured_in b p s) directions.

Definition put_and_flip (b : board) (p : player) (s : nat)
    (captured : list nat) : board :=
  map (fun t => if (t =? s) || existsb (Nat.eqb t) captured
                then Stone p else cell_at b t) squares.

(** All captures are computed in the original board, then applied
    simultaneously.  Occupied squares and moves with no capture fail. *)

Definition play (b : board) (p : player) (s : nat) : option board :=
  if s <? 36 then
    match cell_at b s with
    | Stone _ => None
    | Empty =>
        match flips b p s with
        | [] => None
        | captured => Some (put_and_flip b p s captured)
        end
    end
  else None.

(** The declarative move relation is the graph of the rule function. *)

Definition legal_move (b : board) (p : player) (s : nat) (b' : board) : Prop :=
  In s squares /\ play b p s = Some b'.

Definition moves (b : board) (p : player) : list (nat * board) :=
  flat_map (fun s => match play b p s with
                    | Some b' => [(s, b')]
                    | None => []
                    end) squares.

Definition no_move (b : board) (p : player) : Prop :=
  forall s b', ~ legal_move b p s b'.

Definition has_move (b : board) (p : player) : Prop :=
  exists s b', legal_move b p s b'.

Definition no_moveb (b : board) (p : player) : bool :=
  match moves b p with [] => true | _ => false end.

Definition count (b : board) (p : player) : nat :=
  length (filter (fun c => match c with
                          | Empty => false
                          | Stone q => same_player p q
                          end) b).

Definition terminal (b : board) : Prop :=
  no_move b Black /\ no_move b White.

Definition white_ahead (b : board) : Prop := count b Black < count b White.

Definition initial6 : board :=
  [Empty; Empty; Empty; Empty; Empty; Empty;
   Empty; Empty; Empty; Empty; Empty; Empty;
   Empty; Empty; Stone White; Stone Black; Empty; Empty;
   Empty; Empty; Stone Black; Stone White; Empty; Empty;
   Empty; Empty; Empty; Empty; Empty; Empty;
   Empty; Empty; Empty; Empty; Empty; Empty].

Lemma initial6_well_formed : well_formed initial6.
Proof. reflexivity. Qed.

Lemma play_in_range : forall b p s b',
  play b p s = Some b' -> In s squares.
Proof.
  intros b p s b' H. unfold play in H.
  destruct (s <? 36) eqn:Hs; [|discriminate].
  apply Nat.ltb_lt in Hs. unfold squares. apply in_seq. lia.
Qed.

Lemma play_well_formed : forall b p s b',
  play b p s = Some b' -> well_formed b'.
Proof.
  intros b p s b' H. unfold play in H.
  destruct (s <? 36); [|discriminate].
  destruct (cell_at b s); [|discriminate].
  destruct (flips b p s); [discriminate|].
  injection H as <-.
  unfold well_formed, put_and_flip, squares.
  rewrite length_map, length_seq. reflexivity.
Qed.

Lemma moves_spec : forall b p s b',
  In (s, b') (moves b p) <-> legal_move b p s b'.
Proof.
  intros b p s b'. unfold moves, legal_move.
  rewrite in_flat_map. split.
  - intros [t [Ht Hin]]. destruct (play b p t) as [c|] eqn:Hplay.
    + simpl in Hin. destruct Hin as [Heq|[]].
      inversion Heq; subst. auto.
    + contradiction.
  - intros [Hs Hplay]. exists s. split; [exact Hs|].
    rewrite Hplay. simpl. auto.
Qed.

Lemma no_moveb_spec : forall b p,
  no_moveb b p = true <-> no_move b p.
Proof.
  intros b p. unfold no_moveb, no_move.
  destruct (moves b p) as [|[s c] rest] eqn:Hmoves.
  - split; [|reflexivity]. intros _ t c' Hlegal.
    apply moves_spec in Hlegal. rewrite Hmoves in Hlegal. contradiction.
  - split; [discriminate|]. intros H.
    exfalso. apply (H s c). apply moves_spec. rewrite Hmoves. simpl. auto.
Qed.

Lemma has_moveb_spec : forall b p,
  negb (no_moveb b p) = true <-> has_move b p.
Proof.
  intros b p. unfold no_moveb, has_move.
  destruct (moves b p) as [|[s c] rest] eqn:Hmoves; simpl.
  - split; [discriminate|]. intros [t [c' Hlegal]].
    apply moves_spec in Hlegal. rewrite Hmoves in Hlegal. contradiction.
  - split.
    + intros _. exists s, c. apply moves_spec. rewrite Hmoves. simpl. auto.
    + intros _. reflexivity.
Qed.

(** Operational rules distinguish an actual move from a forced pass.
    There is no transition out of a terminal board. *)

Inductive transition : board -> player -> board -> player -> Prop :=
| transition_move : forall b p s b',
    legal_move b p s b' -> transition b p b' (other p)
| transition_pass : forall b p,
    no_move b p -> has_move b (other p) -> transition b p b (other p).

Lemma transition_preserves_board : forall b p b' q,
  well_formed b -> transition b p b' q -> well_formed b'.
Proof.
  intros b p b' q Hb H. destruct H.
  - destruct H as [_ Hplay]. eapply play_well_formed. exact Hplay.
  - exact Hb.
Qed.
