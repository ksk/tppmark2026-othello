From Stdlib Require Import List ZArith.
From TPP2026.Six Require Import Rules Bounds.
Import ListNotations.

Example initial_legal_moves : map fst (moves initial6 Black) = [8; 13; 22; 27].
Proof. vm_compute; reflexivity. Qed.

Example edges_do_not_wrap : step 5 East = None /\ step 6 West = None.
Proof. split; reflexivity. Qed.

Example initial_count : count initial6 Black = 2 /\ count initial6 White = 2.
Proof. vm_compute; auto. Qed.

Definition terminal20_16 : board :=
  repeat (Stone Black) 16 ++ repeat (Stone White) 20.

Example exact_terminal_score : black_score terminal20_16 = (-4)%Z.
Proof. vm_compute; reflexivity. Qed.

Example correct_lower_accepted :
  check 1 Black (fun b =>
    Z.leb (-4) (black_score b)) terminal20_16 Black CEnd = true.
Proof. vm_compute; reflexivity. Qed.

Example false_lower_rejected :
  check 1 Black (fun b =>
    Z.leb (-3) (black_score b)) terminal20_16 Black CEnd = false.
Proof. vm_compute; reflexivity. Qed.

Example correct_upper_accepted :
  check 1 White (fun b =>
    Z.leb (black_score b) (-4)) terminal20_16 Black CEnd = true.
Proof. vm_compute; reflexivity. Qed.

Example false_upper_rejected :
  check 1 White (fun b =>
    Z.leb (black_score b) (-5)) terminal20_16 Black CEnd = false.
Proof. vm_compute; reflexivity. Qed.

Example insufficient_fuel_rejected :
  check 0 Black (fun _ => true) terminal20_16 Black CEnd = false.
Proof. reflexivity. Qed.

Example missing_responses_rejected :
  check 10 White (fun _ => true) initial6 Black (CAll []) = false.
Proof. vm_compute; reflexivity. Qed.

Example impossible_pass_rejected :
  check 10 Black (fun _ => true) initial6 Black (CPass CEnd) = false.
Proof. vm_compute; reflexivity. Qed.
