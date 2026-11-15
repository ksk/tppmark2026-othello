From Stdlib Require Import List NArith ZArith.
From TPP2026.Six Require Import Rules Bounds Replay Dag InitialSymmetry.
From TPP2026.Six.Semantics Require Import OptimalReplay.
From TPP2026.Six.InitialLower Require Import Goal Links Result.
From TPP2026.Six.InitialUpper Require Import Goal Links Result.
Import ListNotations.

Definition position0 := claim_board (Claim 1081344%N 2113536%N Black).

Lemma value0 : exact_score position0 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B01438.exports
        TPP2026.Six.InitialLower.Links.L01438.certified
      43160560%positive (Claim 1081344%N 2113536%N Black) eq_refl).
  - change (upper_bound initial6 Black (-4)).
    apply initial_upper_from_first8.
    exact TPP2026.Six.InitialUpper.Result.result.
Qed.

Definition position1 := claim_board (Claim 1097984%N 2097152%N White).

Lemma value1 : exact_score position1 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B01438.exports
        TPP2026.Six.InitialLower.Links.L01438.certified
      43160559%positive (Claim 1097984%N 2097152%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B01319.exports
        TPP2026.Six.InitialUpper.Links.L01319.certified
      118749546%positive (Claim 1097984%N 2097152%N White) eq_refl).
Qed.

Definition position2 := claim_board (Claim 49408%N 3670016%N Black).

Lemma value2 : exact_score position2 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B01438.exports
        TPP2026.Six.InitialLower.Links.L01438.certified
      43160558%positive (Claim 49408%N 3670016%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B01319.exports
        TPP2026.Six.InitialUpper.Links.L01319.certified
      118749545%positive (Claim 49408%N 3670016%N Black) eq_refl).
Qed.

Definition position3 := claim_board (Claim 68206848%N 2621440%N White).

Lemma value3 : exact_score position3 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B01438.exports
        TPP2026.Six.InitialLower.Links.L01438.certified
      43160557%positive (Claim 68206848%N 2621440%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00408.exports
        TPP2026.Six.InitialUpper.Links.L00408.certified
      36784098%positive (Claim 68206848%N 2621440%N White) eq_refl).
Qed.

Definition position4 := claim_board (Claim 68157696%N 2671104%N Black).

Lemma value4 : exact_score position4 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B01243.exports
        TPP2026.Six.InitialLower.Links.L01243.certified
      37301645%positive (Claim 68157696%N 2671104%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00408.exports
        TPP2026.Six.InitialUpper.Links.L00408.certified
      36784097%positive (Claim 68157696%N 2671104%N Black) eq_refl).
Qed.

Definition position5 := claim_board (Claim 74481920%N 541184%N White).

Lemma value5 : exact_score position5 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B01243.exports
        TPP2026.Six.InitialLower.Links.L01243.certified
      37301644%positive (Claim 74481920%N 541184%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00408.exports
        TPP2026.Six.InitialUpper.Links.L00408.certified
      36784096%positive (Claim 74481920%N 541184%N White) eq_refl).
Qed.

Definition position6 := claim_board (Claim 74449152%N 639488%N Black).

Lemma value6 : exact_score position6 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00825.exports
        TPP2026.Six.InitialLower.Links.L00825.certified
      24756177%positive (Claim 74449152%N 639488%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00408.exports
        TPP2026.Six.InitialUpper.Links.L00408.certified
      36784095%positive (Claim 74449152%N 639488%N Black) eq_refl).
Qed.

Definition position7 := claim_board (Claim 74482440%N 606208%N White).

Lemma value7 : exact_score position7 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00825.exports
        TPP2026.Six.InitialLower.Links.L00825.certified
      24756176%positive (Claim 74482440%N 606208%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00365.exports
        TPP2026.Six.InitialUpper.Links.L00365.certified
      32929983%positive (Claim 74482440%N 606208%N White) eq_refl).
Qed.

Definition position8 := claim_board (Claim 74481672%N 606980%N Black).

Lemma value8 : exact_score position8 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00739.exports
        TPP2026.Six.InitialLower.Links.L00739.certified
      22170249%positive (Claim 74481672%N 606980%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00365.exports
        TPP2026.Six.InitialUpper.Links.L00365.certified
      32929982%positive (Claim 74481672%N 606980%N Black) eq_refl).
Qed.

Definition position9 := claim_board (Claim 74481934%N 606720%N White).

Lemma value9 : exact_score position9 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00739.exports
        TPP2026.Six.InitialLower.Links.L00739.certified
      22170248%positive (Claim 74481934%N 606720%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00356.exports
        TPP2026.Six.InitialUpper.Links.L00356.certified
      32047043%positive (Claim 74481934%N 606720%N White) eq_refl).
Qed.

Definition position10 := claim_board (Claim 72352014%N 136954368%N Black).

Lemma value10 : exact_score position10 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00737.exports
        TPP2026.Six.InitialLower.Links.L00737.certified
      22122197%positive (Claim 72352014%N 136954368%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00356.exports
        TPP2026.Six.InitialUpper.Links.L00356.certified
      32047042%positive (Claim 72352014%N 136954368%N Black) eq_refl).
Qed.

Definition position11 := claim_board (Claim 8798634766%N 606208%N White).

Lemma value11 : exact_score position11 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00737.exports
        TPP2026.Six.InitialLower.Links.L00737.certified
      22122196%positive (Claim 8798634766%N 606208%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00354.exports
        TPP2026.Six.InitialUpper.Links.L00354.certified
      31924963%positive (Claim 8798634766%N 606208%N White) eq_refl).
Qed.

Definition position12 := claim_board (Claim 8791294734%N 16334848%N Black).

Lemma value12 : exact_score position12 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22074824%positive (Claim 8791294734%N 16334848%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00354.exports
        TPP2026.Six.InitialUpper.Links.L00354.certified
      31924962%positive (Claim 8791294734%N 16334848%N Black) eq_refl).
Qed.

Definition position13 := claim_board (Claim 8792367886%N 15269888%N White).

Lemma value13 : exact_score position13 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22074823%positive (Claim 8792367886%N 15269888%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00354.exports
        TPP2026.Six.InitialUpper.Links.L00354.certified
      31864550%positive (Claim 8792367886%N 15269888%N White) eq_refl).
Qed.

Definition position14 := claim_board (Claim 8792343310%N 15294592%N Black).

Lemma value14 : exact_score position14 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22069778%positive (Claim 8792343310%N 15294592%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00354.exports
        TPP2026.Six.InitialUpper.Links.L00354.certified
      31864549%positive (Claim 8792343310%N 15294592%N Black) eq_refl).
Qed.

Definition position15 := claim_board (Claim 8796734222%N 11034752%N White).

Lemma value15 : exact_score position15 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22069777%positive (Claim 8796734222%N 11034752%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31843362%positive (Claim 8796734222%N 11034752%N White) eq_refl).
Qed.

Definition position16 := claim_board (Claim 8796537614%N 11233408%N Black).

Lemma value16 : exact_score position16 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22065869%positive (Claim 8796537614%N 11233408%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31843361%positive (Claim 8796537614%N 11233408%N Black) eq_refl).
Qed.

Definition position17 := claim_board (Claim 8796604174%N 11167872%N White).

Lemma value17 : exact_score position17 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22065868%positive (Claim 8796604174%N 11167872%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31842100%positive (Claim 8796604174%N 11167872%N White) eq_refl).
Qed.

Definition position18 := claim_board (Claim 8729495310%N 2225760384%N Black).

Lemma value18 : exact_score position18 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064891%positive (Claim 8729495310%N 2225760384%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31842099%positive (Claim 8729495310%N 2225760384%N Black) eq_refl).
Qed.

Definition position19 := claim_board (Claim 8730289934%N 2225227904%N White).

Lemma value19 : exact_score position19 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064890%positive (Claim 8730289934%N 2225227904%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840937%positive (Claim 8730289934%N 2225227904%N White) eq_refl).
Qed.

Definition position20 := claim_board (Claim 8729757454%N 2225764480%N Black).

Lemma value20 : exact_score position20 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064338%positive (Claim 8729757454%N 2225764480%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840936%positive (Claim 8729757454%N 2225764480%N Black) eq_refl).
Qed.

Definition position21 := claim_board (Claim 8747075342%N 2225223808%N White).

Lemma value21 : exact_score position21 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064337%positive (Claim 8747075342%N 2225223808%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840774%positive (Claim 8747075342%N 2225223808%N White) eq_refl).
Qed.

Definition position22 := claim_board (Claim 8730035982%N 3316004992%N Black).

Lemma value22 : exact_score position22 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064310%positive (Claim 8730035982%N 3316004992%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840773%positive (Claim 8730035982%N 3316004992%N Black) eq_refl).
Qed.

Definition position23 := claim_board (Claim 8730036111%N 3316004864%N White).

Lemma value23 : exact_score position23 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064309%positive (Claim 8730036111%N 3316004864%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840614%positive (Claim 8730036111%N 3316004864%N White) eq_refl).
Qed.

Definition position24 := claim_board (Claim 8730034191%N 3316006848%N Black).

Lemma value24 : exact_score position24 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064191%positive (Claim 8730034191%N 3316006848%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840613%positive (Claim 8730034191%N 3316006848%N Black) eq_refl).
Qed.

Definition position25 := claim_board (Claim 8730035247%N 3316005824%N White).

Lemma value25 : exact_score position25 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064190%positive (Claim 8730035247%N 3316005824%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840563%positive (Claim 8730035247%N 3316005824%N White) eq_refl).
Qed.

Definition position26 := claim_board (Claim 8591623215%N 7749385152%N Black).

Lemma value26 : exact_score position26 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064184%positive (Claim 8591623215%N 7749385152%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840562%positive (Claim 8591623215%N 7749385152%N Black) eq_refl).
Qed.

Definition position27 := claim_board (Claim 8591623743%N 7749384640%N White).

Lemma value27 : exact_score position27 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064183%positive (Claim 8591623743%N 7749384640%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840534%positive (Claim 8591623743%N 7749384640%N White) eq_refl).
Qed.

Definition position28 := claim_board (Claim 1689151%N 33519188416%N Black).

Lemma value28 : exact_score position28 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064182%positive (Claim 1689151%N 33519188416%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840533%positive (Claim 1689151%N 33519188416%N Black) eq_refl).
Qed.

Definition position29 := claim_board (Claim 551276095%N 33506472384%N White).

Lemma value29 : exact_score position29 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00735.exports
        TPP2026.Six.InitialLower.Links.L00735.certified
      22064181%positive (Claim 551276095%N 33506472384%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840532%positive (Claim 551276095%N 33506472384%N White) eq_refl).
Qed.

Definition position30 := claim_board (Claim 550751807%N 33540551104%N Black).

Lemma value30 : exact_score position30 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00053.exports
        TPP2026.Six.InitialLower.Links.L00053.certified
      1595869%positive (Claim 550751807%N 33540551104%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840531%positive (Claim 550751807%N 33540551104%N Black) eq_refl).
Qed.

Definition position31 := claim_board (Claim 821284415%N 33538453952%N White).

Lemma value31 : exact_score position31 White (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00016.exports
        TPP2026.Six.InitialLower.Links.L00016.certified
      497453%positive (Claim 821284415%N 33538453952%N White) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00353.exports
        TPP2026.Six.InitialUpper.Links.L00353.certified
      31840528%positive (Claim 821284415%N 33538453952%N White) eq_refl).
Qed.

Definition position32 := claim_board (Claim 550735423%N 68168741312%N Black).

Lemma value32 : exact_score position32 Black (-4).
Proof. split.
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialLower.Goal.who
    TPP2026.Six.InitialLower.Goal.goal)
      TPP2026.Six.InitialLower.B00016.exports
        TPP2026.Six.InitialLower.Links.L00016.certified
      497452%positive (Claim 550735423%N 68168741312%N Black) eq_refl).
  - exact (lookup_all claim (valid_claim TPP2026.Six.InitialUpper.Goal.who
    TPP2026.Six.InitialUpper.Goal.goal)
      TPP2026.Six.InitialUpper.B00022.exports
        TPP2026.Six.InitialUpper.Links.L00022.certified
      2022338%positive (Claim 550735423%N 68168741312%N Black) eq_refl).
Qed.

Definition meeting_actions : list (option nat) :=
  [Some 8; Some 19; Some 26; Some 9; Some 22; Some 16; Some 3; Some 2;
   Some 1; Some 27; Some 33; Some 23; Some 13; Some 7; Some 17; Some 11;
   Some 10; Some 31; Some 18; Some 12; Some 24; Some 30; Some 0; Some 6;
   Some 5; Some 32; Some 4; Some 34; Some 29; Some 25; Some 28; Some 35].

Theorem meeting_is_optimal : optimal_replay (-4) position0 Black
  meeting_actions.
Proof.
  unfold meeting_actions.
  eapply (optimal_step (-4) _ _ (Some 8) position1 White);
    [exact value0|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 19) position2 Black);
    [exact value1|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 26) position3 White);
    [exact value2|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 9) position4 Black);
    [exact value3|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 22) position5 White);
    [exact value4|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 16) position6 Black);
    [exact value5|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 3) position7 White);
    [exact value6|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 2) position8 Black);
    [exact value7|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 1) position9 White);
    [exact value8|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 27) position10 Black);
    [exact value9|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 33) position11 White);
    [exact value10|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 23) position12 Black);
    [exact value11|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 13) position13 White);
    [exact value12|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 7) position14 Black);
    [exact value13|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 17) position15 White);
    [exact value14|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 11) position16 Black);
    [exact value15|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 10) position17 White);
    [exact value16|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 31) position18 Black);
    [exact value17|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 18) position19 White);
    [exact value18|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 12) position20 Black);
    [exact value19|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 24) position21 White);
    [exact value20|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 30) position22 Black);
    [exact value21|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 0) position23 White);
    [exact value22|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 6) position24 Black);
    [exact value23|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 5) position25 White);
    [exact value24|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 32) position26 Black);
    [exact value25|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 4) position27 White);
    [exact value26|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 34) position28 Black);
    [exact value27|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 29) position29 White);
    [exact value28|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 25) position30 Black);
    [exact value29|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 28) position31 White);
    [exact value30|vm_compute; reflexivity|].
  eapply (optimal_step (-4) _ _ (Some 35) position32 Black);
    [exact value31|vm_compute; reflexivity|].
  apply optimal_end; [exact value32|].
  split; apply no_moveb_spec; vm_compute; reflexivity.
Qed.

Theorem meeting_replay_checked : replay position0 Black meeting_actions = Some
  (position32, Black).
Proof. vm_compute; reflexivity. Qed.

Theorem meeting_final_counts : count position32 Black = 16 /\
  count position32 White = 20.
Proof. vm_compute; auto. Qed.

Corollary initial6_exact_score : exact_score initial6 Black (-4).
Proof. exact value0. Qed.

Theorem initial6_optimal_20_16 : exists actions c q,
  optimal_replay (-4) initial6 Black actions /\
  replay initial6 Black actions = Some (c, q) /\ terminal c /\
  count c Black = 16 /\ count c White = 20.
Proof.
  exists meeting_actions, position32, Black.
  split; [exact meeting_is_optimal|].
  split; [exact meeting_replay_checked|].
  split.
  - split; apply no_moveb_spec; vm_compute; reflexivity.
  - exact meeting_final_counts.
Qed.
