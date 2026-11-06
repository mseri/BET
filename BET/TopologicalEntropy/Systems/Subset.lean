/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.Subset

/-!
# Topological entropy of subsets: monotonicity, closure
Proof that the topological entropy depends monotonically on the subset. Main results
are `Dynamics.coverEntropyInf_monotone` and `Dynamics.coverEntropy_monotone`.
The intermediate cover and net entourage-entropy results are also provided by mathlib,
since they may be useful in the study of other systems.

For uniformly continuous maps, proof that the entropy of a subset is the entropy of its closure.
Main results are `Dynamics.coverEntropyInf_closure` and `Dynamics.coverEntropy_closure`;
mathlib proves these with the weaker hypothesis of continuity.

TODO: I think one could implement a notion of Hausdorff convergence for subsets using uniform
spaces, and then prove the semicontinuity of the topological entropy. It would be a nice
generalization of these lemmas on closures.
-/
