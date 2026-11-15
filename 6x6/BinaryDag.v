From Stdlib Require Import List NArith.
From TPP2026.Six Require Import Rules Dag.
Import ListNotations.

(** Untrusted data are packed as ordinary positive constructors. The semantic
    checker remains responsible for accepting or rejecting decoded entries. *)

Definition bit_tail (p : positive) :=
  match p with xI q | xO q => q | xH => xH end.

Fixpoint read_bits (fuel : nat) (p : positive) : N * positive :=
  match fuel with
  | O => (0%N, p)
  | S n => let ' (v, q) := read_bits n (bit_tail p) in
      (match p with xO _ => N.double v | _ => N.succ_double v end, q)
  end.

Definition bit_id (n : N) := match n with N0 => 1%positive | Npos p => p end.

Fixpoint read_children (n : nat) (p : positive) : list positive :=
  match n with
  | O => []
  | S n' => let ' (id, q) := read_bits 32 p in bit_id id :: read_children n' q
  end.

Definition decode_word (p : positive) : entry :=
  let ' (id, p1) := read_bits 32 p in
  let ' (bb, p2) := read_bits 36 p1 in
  let ' (wb, p3) := read_bits 36 p2 in
  let ' (turn, p4) := read_bits 1 p3 in
  let ' (action, p5) := read_bits 6 p4 in
  let ' (count, p6) := read_bits 6 p5 in
  let children := read_children (N.to_nat count) p6 in
  let op :=
    if N.eqb action 0 then DEnd
    else if N.eqb action 37 then DAll children
    else if N.eqb action 38 then DPass (hd 1%positive children)
    else DChoose (Nat.pred (N.to_nat action)) (hd 1%positive children)
  in
  Entry (bit_id id) (Claim bb wb (if N.eqb turn 0 then Black else White)) op.
