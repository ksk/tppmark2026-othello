From TPP2026.Four Require Export Rules.
From TPP2026.Common.Proofs Require Import GameFacts SpecificationFacts.

(** Instantiate the common definitions for a 4x4 board. Rules supplies
    the square-content, colour and direction types. The equivalence proof
    for the certificate rules is in proofs/equivalence/Four.v. *)
Module Four <: TPP2026.Common.Rules.Dimension.
  Definition side := 4.

End Four.
Module Export Board4 := GameFacts.Make TPP2026.Four.Rules Four.
Module Spec4 := SpecificationFacts.Make TPP2026.Four.Rules Four.
