/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.DynamicalEntourage

/-!
# Dynamical entourages
We implement Bowen-Dinaburg's definitions of the topological entropy. The most common version
of this definition uses metric spaces and then defines dynamical balls. To get a more flexible
version of topological entropy, we work instead with uniform spaces. Dynamical balls are
replaced by dynamical entourages (called dynamical uniformities in the original development).

The core development is now provided by mathlib as `Dynamics.dynEntourage`.
This file retains the product-entourage helpers used by the product estimates.
-/

@[expose] public section

namespace DynamicalUniformity

open Dynamics UniformSpace

/-- Product of two entourages, with the coordinates regrouped. -/
def UniformityProd {X Y : Type*} (U : Set (X × X)) (V : Set (Y × Y)) :
    Set ((X × Y) × (X × Y)) :=
  {p | (p.1.1, p.2.1) ∈ U ∧ (p.1.2, p.2.2) ∈ V}

lemma ball_prod {X Y : Type*} (U : Set (X × X)) (V : Set (Y × Y)) (xy : X × Y) :
    ball xy (UniformityProd U V) = ball xy.1 U ×ˢ ball xy.2 V := rfl

lemma dynamical_uni_prod {X Y : Type*} (S : X → X) (T : Y → Y)
    (U : Set (X × X)) (V : Set (Y × Y)) (n : ℕ) :
    dynEntourage (Prod.map S T) (UniformityProd U V) n =
      UniformityProd (dynEntourage S U n) (dynEntourage T V n) := by
  ext ⟨⟨x, y⟩, ⟨x', y'⟩⟩
  simp only [mem_dynEntourage, UniformityProd, Set.mem_ofPred_eq, Prod.map_iterate,
    Prod.map_apply]
  simp only [forall_and]

end DynamicalUniformity
