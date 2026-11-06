/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.Semiconj
public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of the image of a set under a semiconjugacy
The main lemmas are `Dynamics.coverEntropyInf_image_of_comap` and
`Dynamics.coverEntropy_image_of_comap`: the entropy of the image of a set by a
semiconjugacy is the entropy of the set for the inverse image uniform structure.
These lemmas need very few hypotheses, and generalize many important results.

First, a uniformly continuous semiconjugacy decreases the entropy of subsets:
`Dynamics.coverEntropyInf_image_le_of_uniformContinuous` and
`Dynamics.coverEntropy_image_le_of_uniformContinuous`.

Second, the entropy of `Set.univ` for a subsystem is equal to the entropy of the subset, which
justifies the implementation of the entropy of a subset: `Dynamics.coverEntropy_restrict`.

Cover and global entropy results are provided by mathlib. This file retains the
net-specific lifting and comparison results, using mathlib's entropy definitions.

TODO: Investigate the consequences of the image-entropy equalities for embeddings.

TODO: There are some interesting related results about the entropy of fibered systems.
-/

public section

namespace EntropyImage

open Function UniformSpace Dynamics Set

variable {X Y : Type*} {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T)

include h

lemma preimage_of_dynamical_net {F : Set X} {V : Set (Y × Y)} {n : ℕ} {t : Finset Y}
    (ht : IsDynNetIn T (φ '' F) V n t) :
    ∃ s : Finset X, IsDynNetIn S F (Prod.map φ φ ⁻¹' V) n s ∧ t.card ≤ s.card := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | htne
  · exact ⟨∅, by simpa using (isDynNetIn_empty (T := S) (F := F)
      (U := Prod.map φ φ ⁻¹' V) (n := n)), by simp⟩
  have hF : F.Nonempty := Set.Nonempty.of_image (Set.Nonempty.mono ht.1 htne)
  have : Nonempty X := hF.to_type
  have key : ∀ y ∈ t, ∃ x ∈ F, φ x = y := fun y hy => ht.1 hy
  choose! f hf using key
  refine ⟨t.image f, ⟨?_, ?_⟩, ?_⟩
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (hf y hy).1
  · apply Set.pairwiseDisjoint_iff.mpr
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z, hzx, hzy⟩ := hxy
    have hxball : φ z ∈ ball x' (dynEntourage T V n) := by
      rw [← (hf x' hx').2]
      simpa [ball, ← h.preimage_dynEntourage V n] using hzx
    have hyball : φ z ∈ ball y' (dynEntourage T V n) := by
      rw [← (hf y' hy').2]
      simpa [ball, ← h.preimage_dynEntourage V n] using hzy
    exact congrArg f (ht.2.elim_set hx' hy' (φ z) hxball hyball)
  · have hsub : t ⊆ (t.image f).image φ := by
      intro y hy
      exact Finset.mem_image.mpr ⟨f y, Finset.mem_image_of_mem f hy, (hf y hy).2⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le

lemma image_maxcard (F : Set X) (V : Set (Y × Y)) (n : ℕ) :
    netMaxcard T (φ '' F) V n ≤ netMaxcard S F (Prod.map φ φ ⁻¹' V) n := by
  apply iSup₂_le
  intro t ht
  obtain ⟨s, hs, hcard⟩ := preimage_of_dynamical_net h ht
  exact (Nat.cast_le.mpr hcard).trans hs.card_le_netMaxcard

lemma image_net_entropy (F : Set X) (V : Set (Y × Y)) :
    netEntropyInfEntourage T (φ '' F) V ≤ netEntropyInfEntourage S F (Prod.map φ φ ⁻¹' V) :=
  ExpGrowth.expGrowthInf_monotone fun n => ENat.toENNReal_mono (image_maxcard h F V n)

lemma image_net_entropy' (F : Set X) (V : Set (Y × Y)) :
    netEntropyEntourage T (φ '' F) V ≤ netEntropyEntourage S F (Prod.map φ φ ⁻¹' V) :=
  ExpGrowth.expGrowthSup_monotone fun n => ENat.toENNReal_mono (image_maxcard h F V n)

end EntropyImage
