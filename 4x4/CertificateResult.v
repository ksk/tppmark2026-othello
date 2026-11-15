From TPP2026.Four Require Import Rules Bounds Certificate.

(** This is an actual kernel-checked computation, not an assumption
    about the external Python generator or its search result. *)

Lemma certificate4_checked :
  check certificate4_fuel initial4 Black certificate4 = true.
Proof. vm_compute; reflexivity. Qed.

(** TPP-mark 2026, problem 1: White can force a strict win from the
    standard 4 x 4 initial position, whatever legal choices Black makes. *)

Theorem othello4_white_wins : white_wins initial4 Black.
Proof.
  exact (check_sound certificate4_fuel initial4 Black
           certificate4 certificate4_checked).
Qed.

Print Assumptions check_sound.
Print Assumptions certificate4_checked.
Print Assumptions othello4_white_wins.
