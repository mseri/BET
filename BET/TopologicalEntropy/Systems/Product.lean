/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
public import BET.TopologicalEntropy.DynamicalUniformity

/-!
# Topological entropy estimates for products

Products of covers give a limsup entourage-entropy upper bound; products of nets
give a liminf entourage-entropy lower bound. The global product-entropy formula,
which additionally requires taking suprema over product entourages, is not proved here.

TODO: Ease the manipulation of products of uniformities. Maybe complete the file on uniform spaces.

TODO: Finish the proofs. We have the right estimates on cover and net entourage entropy; all that
is left is to take the supremum over entourages, using the description of the uniform structure
on a product.

TODO: Extend it to finite products.
-/

public section

open Dynamics DynamicalUniformity
open scoped ENNReal

namespace DynamicalCoverProduct

lemma cover_of_product {X Y : Type*} {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y}
    {U : Set (X × X)} {V : Set (Y × Y)} {n : ℕ} {s : Set X} {t : Set Y}
    (hs : IsDynCoverOf S F U n s) (ht : IsDynCoverOf T G V n t) :
    IsDynCoverOf (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n (s ×ˢ t) := by
  intro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨a, ha, hxa⟩ := hs hx
  obtain ⟨b, hb, hyb⟩ := ht hy
  refine ⟨(a, b), ⟨ha, hb⟩, ?_⟩
  rw [dynamical_uni_prod]
  exact ⟨hxa, hyb⟩

lemma cover_mincard_product {X Y : Type*} (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) (n : ℕ) :
    coverMincard (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n ≤
      coverMincard S F U n * coverMincard T G V n := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  rcases G.eq_empty_or_nonempty with rfl | hG
  · simp
  rcases eq_top_or_lt_top (coverMincard S F U n) with hS | hS
  · rw [hS, ENat.top_mul (ne_of_gt (zero_lt_one.trans_le ((one_le_coverMincard_iff T G V n).2 hG)))]
    exact le_top
  rcases eq_top_or_lt_top (coverMincard T G V n) with hT | hT
  · rw [hT, ENat.mul_top (ne_of_gt (zero_lt_one.trans_le ((one_le_coverMincard_iff S F U n).2 hF)))]
    exact le_top
  obtain ⟨s, hs, hsc⟩ := (coverMincard_finite_iff S F U n).mp hS
  obtain ⟨t, ht, htc⟩ := (coverMincard_finite_iff T G V n).mp hT
  rw [← hsc, ← htc, ← Nat.cast_mul, ← Finset.card_product]
  exact (show IsDynCoverOf (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n
    (s ×ˢ t : Finset (X × Y)) by
      simpa only [Finset.coe_product] using cover_of_product hs ht).coverMincard_le_card

/-- The limsup cover entropy of a product entourage is subadditive. -/
lemma cover_entropy'_product {X Y : Type*} (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) :
    coverEntropyEntourage (Prod.map S T) (F ×ˢ G) (UniformityProd U V) ≤
      coverEntropyEntourage S F U + coverEntropyEntourage T G V := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  rcases G.eq_empty_or_nonempty with rfl | hG
  · simp
  apply le_trans (ExpGrowth.expGrowthSup_monotone fun n => ?_)
    (ExpGrowth.expGrowthSup_mul_le
      (Or.inl (ne_of_gt (EReal.bot_lt_zero.trans_le (coverEntropyEntourage_nonneg S hF U))))
      (Or.inr (ne_of_gt (EReal.bot_lt_zero.trans_le (coverEntropyEntourage_nonneg T hG V)))))
  simpa only [Pi.mul_apply, ← ENat.toENNReal_mul] using
    ENat.toENNReal_mono (cover_mincard_product S T F G U V n)

end DynamicalCoverProduct

namespace NetEntropyProduct

open UniformSpace

lemma net_of_product {X Y : Type*} {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y}
    {U : Set (X × X)} {V : Set (Y × Y)} {n : ℕ} {s : Set X} {t : Set Y}
    (hs : IsDynNetIn S F U n s) (ht : IsDynNetIn T G V n t) :
    IsDynNetIn (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n (s ×ˢ t) := by
  refine ⟨Set.prod_mono hs.1 ht.1, ?_⟩
  simpa only [dynamical_uni_prod, ball_prod] using hs.2.prod ht.2

lemma net_maxcard_product {X Y : Type*} (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) (n : ℕ) :
    netMaxcard S F U n * netMaxcard T G V n ≤
      netMaxcard (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  rcases G.eq_empty_or_nonempty with rfl | hG
  · simp
  rcases eq_top_or_lt_top (netMaxcard S F U n) with hS | hS
  · have hprod : netMaxcard (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n = ⊤ := by
      apply (netMaxcard_infinite_iff _ _ _ _).mpr
      intro k
      obtain ⟨s, hs, hcard⟩ := (netMaxcard_infinite_iff S F U n).mp hS k
      obtain ⟨y, hy⟩ := hG
      refine ⟨s ×ˢ {y}, ?_, by simpa using hcard⟩
      simpa only [Finset.coe_product, Finset.coe_singleton] using
        net_of_product hs (isDynNetIn_singleton T V n hy)
    rw [hprod]
    exact le_top
  rcases eq_top_or_lt_top (netMaxcard T G V n) with hT | hT
  · have hprod : netMaxcard (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n = ⊤ := by
      apply (netMaxcard_infinite_iff _ _ _ _).mpr
      intro k
      obtain ⟨t, ht, hcard⟩ := (netMaxcard_infinite_iff T G V n).mp hT k
      obtain ⟨x, hx⟩ := hF
      refine ⟨{x} ×ˢ t, ?_, by simpa using hcard⟩
      simpa only [Finset.coe_product, Finset.coe_singleton] using
        net_of_product (isDynNetIn_singleton S U n hx) ht
    rw [hprod]
    exact le_top
  obtain ⟨s, hs, hsc⟩ := (netMaxcard_finite_iff S F U n).mp hS
  obtain ⟨t, ht, htc⟩ := (netMaxcard_finite_iff T G V n).mp hT
  rw [← hsc, ← htc, ← Nat.cast_mul, ← Finset.card_product]
  exact (show IsDynNetIn (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n
    (s ×ˢ t : Finset (X × Y)) by
      simpa only [Finset.coe_product] using net_of_product hs ht).card_le_netMaxcard

/-- The liminf net entropy of a product entourage is superadditive. -/
lemma net_entropy_product {X Y : Type*} (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) :
    netEntropyInfEntourage S F U + netEntropyInfEntourage T G V ≤
      netEntropyInfEntourage (Prod.map S T) (F ×ˢ G) (UniformityProd U V) := by
  apply le_trans ExpGrowth.le_expGrowthInf_mul
    (ExpGrowth.expGrowthInf_monotone fun n => ?_)
  simpa only [Pi.mul_apply, ← ENat.toENNReal_mul] using
    ENat.toENNReal_mono (net_maxcard_product S T F G U V n)

end NetEntropyProduct
