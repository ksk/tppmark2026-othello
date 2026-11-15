From Stdlib Require Import List.
From TPP2026.Four Require Import Rules Bounds Certificate.
Import ListNotations.

(** Rule-level examples use explicit expected positions, independently
    of the Python generator. *)
Example initial_black_moves : map fst (moves initial4 Black) = [1; 4; 11; 14].
Proof. vm_compute; reflexivity. Qed.

Example initial_white_moves : map fst (moves initial4 White) = [2; 7; 8; 13].
Proof. vm_compute; reflexivity. Qed.

Example black_b1 : play initial4 Black 1 = Some
  [Empty; Stone Black; Empty; Empty;
   Empty; Stone Black; Stone Black; Empty;
   Empty; Stone Black; Stone White; Empty;
   Empty; Empty; Empty; Empty].
Proof. vm_compute; reflexivity. Qed.

Example occupied_square_rejected : play initial4 Black 5 = None.
Proof. vm_compute; reflexivity. Qed.

Example no_capture_rejected : play initial4 Black 0 = None.
Proof. vm_compute; reflexivity. Qed.

Example outside_board_rejected : play initial4 White 16 = None.
Proof. vm_compute; reflexivity. Qed.

Example no_row_wrap_east : step 3 East = None.
Proof. reflexivity. Qed.

Example no_row_wrap_west : step 4 West = None.
Proof. reflexivity. Qed.

Definition three_directions : board :=
  [Empty; Empty; Empty; Empty;
   Empty; Empty; Stone Black; Stone White;
   Empty; Stone Black; Stone Black; Empty;
   Empty; Stone White; Empty; Stone White].

Example captures_all_directions :
  flips three_directions White 5 = [6; 10; 9].
Proof. vm_compute; reflexivity. Qed.

Example flips_are_simultaneous : play three_directions White 5 = Some
  [Empty; Empty; Empty; Empty;
   Empty; Stone White; Stone White; Stone White;
   Empty; Stone White; Stone White; Empty;
   Empty; Stone White; Empty; Stone White].
Proof. vm_compute; reflexivity. Qed.

Definition black_must_pass : board :=
  [Empty; Empty; Empty; Stone Black;
   Stone White; Stone White; Stone Black; Stone White;
   Empty; Stone White; Stone White; Stone White;
   Stone Black; Stone White; Stone White; Stone White].

Example only_black_has_no_move :
  no_moveb black_must_pass Black = true /\
  map fst (moves black_must_pass White) = [1; 2].
Proof. vm_compute; auto. Qed.

Example forced_pass_is_a_transition :
  transition black_must_pass Black black_must_pass White.
Proof.
  apply transition_pass.
  - apply no_moveb_spec. vm_compute; reflexivity.
  - apply has_moveb_spec. vm_compute; reflexivity.
Qed.

Definition white_only : board := Empty :: repeat (Stone White) 15.

Example game_can_end_before_board_full :
  no_moveb white_only Black = true /\ no_moveb white_only White = true.
Proof. vm_compute; auto. Qed.

Example terminal_win_accepted : check 1 white_only Black CEnd = true.
Proof. vm_compute; reflexivity. Qed.

Example terminal_cannot_pass : check 2 white_only Black (CPass CEnd) = false.
Proof. vm_compute; reflexivity. Qed.

Example draw_is_not_a_white_win :
  check 1 (repeat (Stone Black) 8 ++ repeat (Stone White) 8) White CEnd = false.
Proof. vm_compute; reflexivity. Qed.

(** Adversarial certificates: do not accept vacuous wins, illegal passes,
    incorrect players, unfinished games or an exhausted computation. *)
Example missing_black_replies_rejected :
  check 20 initial4 Black (CBlack []) = false.
Proof. vm_compute; reflexivity. Qed.

Example dropping_one_reply_rejected :
  match certificate4 with
  | CBlack (_ :: rest) => check 20 initial4 Black (CBlack rest)
  | _ => true
  end = false.
Proof. vm_compute; reflexivity. Qed.

Example extra_reply_rejected :
  match certificate4 with
  | CBlack replies => check 20 initial4 Black (CBlack (replies ++ [CEnd]))
  | _ => true
  end = false.
Proof. vm_compute; reflexivity. Qed.

Example premature_terminal_rejected : check 20 initial4 Black CEnd = false.
Proof. vm_compute; reflexivity. Qed.

Example voluntary_pass_rejected :
  check 20 initial4 Black (CPass certificate4) = false.
Proof. vm_compute; reflexivity. Qed.

Example wrong_player_rejected :
  check 20 initial4 Black (CWhite 2 CEnd) = false.
Proof. vm_compute; reflexivity. Qed.

Example no_fuel_rejected : check 0 initial4 Black certificate4 = false.
Proof. reflexivity. Qed.
