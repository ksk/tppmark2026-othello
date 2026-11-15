From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

(** The same rules are used for both board sizes.  [Pieces] is a type
    adapter for the already checked certificates, not a choice of rules. *)
Module Type Pieces.
  Inductive player := Black | White.
  Inductive cell := Empty | Stone (p : player).
  Inductive direction :=
    North | NorthEast | East | SouthEast | South | SouthWest | West | NorthWest.

End Pieces.

Module Type Dimension.
  Parameter side : nat.

End Dimension.

Module Make (P : Pieces) (D : Dimension).
Import P.

Definition side := D.side.

Definition area := side * side.

Definition board := list cell.

Definition other (p : player) : player :=
  match p with Black => White | White => Black end.

Definition same_player (p q : player) : bool :=
  match p, q with Black, Black | White, White => true | _, _ => false end.

Definition squares : list nat := seq 0 area.

Definition well_formed (b : board) : Prop := length b = area.

Definition cell_at (b : board) (s : nat) : cell := nth s b Empty.

(** Standard central opening, specialized below to the even sizes 4 and 6.
    Squares are numbered by row, starting at the top left. *)

Definition initial : board :=
  let lo := side / 2 - 1 in
  let hi := side / 2 in
  map (fun s =>
    let r := s / side in let c := s mod side in
    if ((r =? lo) && (c =? lo)) || ((r =? hi) && (c =? hi))
    then Stone White
    else if ((r =? lo) && (c =? hi)) || ((r =? hi) && (c =? lo))
    then Stone Black else Empty) squares.

Definition directions :=
  [North; NorthEast; East; SouthEast; South; SouthWest; West; NorthWest].

(** One geometric step, with explicit row/column boundary checks. *)

Definition step (s : nat) (d : direction) : option nat :=
  if s <? area then
    let r := s / side in
    let c := s mod side in
    match d with
    | North => if 0 <? r then Some (s - side) else None
    | NorthEast =>
      if (0 <? r) && (c <? side - 1) then Some (s - (side - 1)) else None
    | East => if c <? side - 1 then Some (s + 1) else None
    | SouthEast =>
      if (r <? side - 1) && (c <? side - 1) then Some (s + (side + 1)) else None
    | South => if r <? side - 1 then Some (s + side) else None
    | SouthWest =>
      if (r <? side - 1) && (0 <? c) then Some (s + (side - 1)) else None
    | West => if 0 <? c then Some (s - 1) else None
    | NorthWest => if (0 <? r) && (0 <? c) then Some (s - (side + 1)) else None
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
  match bracket b p (ray (side - 1) s d) with
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
  if s <? area then
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

(** Operational rules distinguish an actual move from a forced pass.
    There is no transition out of a terminal board. *)

Inductive transition : board -> player -> board -> player -> Prop :=
| transition_move : forall b p s b',
    legal_move b p s b' -> transition b p b' (other p)
| transition_pass : forall b p,
    no_move b p -> has_move b (other p) -> transition b p b (other p).


End Make.
