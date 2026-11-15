From Stdlib Require Import List Bool Arith Lia.
From TPP2026.Common Require Import Rules.
Import ListNotations.

(** A relational description of captures.  This specification does not call
    [bracket], [flips] or [play]; the theorems connect it to those functions. *)
Module Make (P : Rules.Pieces) (D : Rules.Dimension).
Module R := Rules.Make P D.
Include R.
Import P.

Inductive bracketed (b : board) (p : player) : list nat -> list nat -> Prop :=
| bracket_stop : forall s rest,
    cell_at b s = Stone p -> bracketed b p (s :: rest) []
| bracket_extend : forall s rest captured,
    cell_at b s = Stone (other p) ->
    bracketed b p rest captured ->
    bracketed b p (s :: rest) (s :: captured).

Definition captures (b : board) (p : player) (s t : nat) : Prop :=
  exists d captured,
    In d directions /\ bracketed b p (ray (side - 1) s d) captured /\
      In t captured.

(** All directions are evaluated on the original board.  The resulting board
    changes exactly the played square and the captured squares. *)

Definition legal_spec (b : board) (p : player) (s : nat) (b' : board) : Prop :=
  exists captured,
    s < area /\ cell_at b s = Empty /\ captured <> [] /\
    (forall t, In t captured <-> captures b p s t) /\
    b' = map (fun t => if (t =? s) || existsb (Nat.eqb t) captured
                      then Stone p else cell_at b t) squares.


End Make.
