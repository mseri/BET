/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.Subset

/-!
# Topological entropy of unions
The topological entropy of a union is the maximum of the topological entropies.
Here the entropy uses limsup, as in the original primed statements.

Mathlib proves `Dynamics.coverMincard_union_le`,
`Dynamics.coverEntropyEntourage_union`, and `Dynamics.coverEntropy_union`,
replacing the former local development (including its unfinished proofs).
The extension to finite unions is also provided by mathlib.
-/
