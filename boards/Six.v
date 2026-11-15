From TPP2026.Six Require Export Rules.
From TPP2026.Common.Proofs Require Import GameFacts SpecificationFacts.

(** Instantiate the common definitions for a 6x6 board. Six.Rules supplies
    the square-content, colour and direction types. The equivalence proof
    for the certificate rules is in proofs/equivalence/Six.v. *)
Module Six <: TPP2026.Common.Rules.Dimension.
  Definition side := 6.

End Six.
Module Export Board6 := GameFacts.Make TPP2026.Six.Rules Six.
Module Spec6 := SpecificationFacts.Make TPP2026.Six.Rules Six.
