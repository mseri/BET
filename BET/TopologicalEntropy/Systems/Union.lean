/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import BET.TopologicalEntropy.Systems.Subset


/-!
# Topological entropy of unions
The topological entropy of an union is the maximum of the topological entropies.

TODO: Finish the proof. The manipulation of logarithms and limits is still too painful.

TODO: extend it to finite unions.
-/

namespace EntropyUnion

open ERealDiv ENNReal Misc DynamicalCover EntropyMonotoneSpace

variable {X : Type _}

theorem cover_of_union {T : X → X} {F G : Set X} {U : Set (X × X)} {n : ℕ} {s t : Set X}
    (hs : IsDynamicalCoverOf T F U n s) (ht : IsDynamicalCoverOf T G U n t) :
    IsDynamicalCoverOf T (F ∪ G) U n (s ∪ t) := by
  intro x x_in_FG
  rcases x_in_FG with (x_in_F | x_in_G)
  . specialize hs x_in_F
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at hs
    rcases hs with ⟨y, ⟨y_in_s, hy⟩⟩
    simp only [Set.iUnion_coe_set, Set.mem_union, Set.mem_iUnion, exists_prop]
    use y
    exact ⟨Or.inl y_in_s, hy⟩
  . specialize ht x_in_G
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at ht
    rcases ht with ⟨y, ⟨y_in_t, hy⟩⟩
    simp only [Set.iUnion_coe_set, Set.mem_union, Set.mem_iUnion, exists_prop]
    use y
    exact ⟨Or.inr y_in_t, hy⟩

theorem cover_mincard_union (T : X → X) (F G : Set X) (U : Set (X × X)) (n : ℕ) :
    Mincard T (F ∪ G) U n ≤ Mincard T F U n + Mincard T G U n := by
  classical
  /-WLOG, `F` admits a finite cover.-/
  rcases eq_top_or_lt_top (Mincard T F U n) with F_infi | F_fin
  . rw [F_infi, top_add]; exact le_top
  /-WLOG, `G` admits a finite cover.-/
  rcases eq_top_or_lt_top (Mincard T G U n) with G_infi | G_fin
  . rw [G_infi, add_top]; exact le_top
  /-Get some minimal covers of `F` and `G`.-/
  rw [finite_mincard_iff T F U n] at F_fin
  rcases F_fin with ⟨s, ⟨s_cover, s_mincard⟩⟩
  rw [← s_mincard]; clear s_mincard
  rw [finite_mincard_iff T G U n] at G_fin
  rcases G_fin with ⟨t, ⟨t_cover, t_mincard⟩⟩
  rw [← t_mincard]; clear t_mincard
  /-Construct a cover of `F ×ˢ G` and show that is has the right cardinality-/
  have := cover_of_union s_cover t_cover
  rw [← Finset.coe_union s t] at this
  apply le_trans (mincard_le_card this) (le_trans (WithTop.coe_mono (Finset.card_union_le s t)) _)
  simp
/-
theorem cover_entropy'_union (T : X → X) (F G : Set X) (U : Set (X × X)) :
    CoverEntropy' T (F ∪ G) U = max (CoverEntropy' T F U) (CoverEntropy' T G U) := by
  classical
  /-WLOG, `F` admits a finite cover.-/
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  · simp only [Set.empty_union, cover_entropy'_of_empty, bot_le, max_eq_right]
  /-WLOG, `G` admits a finite cover.-/
  rcases G.eq_empty_or_nonempty with (rfl | G_nemp)
  · simp only [Set.union_empty, cover_entropy'_of_empty, bot_le, max_eq_left]
  /-One inequality follows trivially from the monotonicity of the entropy.-/
  apply le_antisymm _ (max_le (cover_entropy'_monotone_space T U (Set.subset_union_left F G))
    (cover_entropy'_monotone_space T U (Set.subset_union_right F G)))
  simp only
  /-Main case.-/
  have nneg_log_max := fun n : ℕ => log_monotone (ENat.toENNReal_le.2 (le_trans
    ((pos_mincard_of_nonempty T F U n).1 F_nemp) (le_max_left (Mincard T F U n) (Mincard T G U n)) ) )
  simp at nneg_log_max
  have key : ∀ n : ℕ, ENNReal.log (Mincard T (F ∪ G) U n) / (n : ENNReal)
    ≤ ENNReal.log (2) / (n : ENNReal)
    + ENNReal.log (max (Mincard T F U n) (Mincard T G U n)) / (n : ENNReal) := by
    intro n
    rw [← @EReal.div_right_distrib_of_nneg _ _ n (log_one_le_iff.1 one_le_two) (nneg_log_max n)]
    apply EReal.div_left_mono n
    rw [← log_mul_add]
    apply log_monotone
    apply le_trans (ENat.toENNReal_le.2 (cover_mincard_union T F G U n))
    rw [two_mul, ENat.toENNReal_add]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)
  apply le_trans (Filter.limsup_le_limsup (@Filter.eventually_of_forall ℕ _ Filter.atTop key))
  clear key
  apply le_trans (EReal.limsup_add_le_add_limsup _ _)
  . have limsup_zero : Filter.limsup (fun n : ℕ => log 2 / (n : ENNReal)) Filter.atTop = 0 := by
      apply Filter.Tendsto.limsup_eq
      have : (fun n : ℕ => log (2) / (n : ENNReal))
        = (fun p : EReal × EReal => p.1 * p.2)
        ∘ (fun n : ℕ => Prod.mk (ENNReal.log (2)) ((n⁻¹ : ENNReal) : EReal)) := by
        ext n
        simp
        sorry
      have log_ne_zero : ENNReal.log (2) ≠ 0 := by sorry
      have log_ne_bot : ENNReal.log (2) ≠ ⊥ := by sorry
      have log_ne_top : ENNReal.log (2) ≠ ⊤ := by sorry
      have key := @ERealMulCont.continuousAt_mul (log (2), 0)
        (Or.inl log_ne_zero) (Or.inl log_ne_zero) (Or.inl log_ne_bot) (Or.inl log_ne_top)
      replace key := ContinuousAt.tendsto key
      simp at key
      sorry
    unfold CoverEntropy'
    rw [limsup_zero, zero_add, ← EReal.limsup_max]; clear limsup_zero
    apply Filter.limsup_le_limsup
    . apply Filter.eventually_of_forall
      intro n
      simp only []
      rw [← Monotone.map_max (EReal.div_left_mono n)]
      apply EReal.div_left_mono n
      rw [Monotone.map_max log_monotone]
    . use ⊥; simp
    . use ⊤; simp
  . apply Or.inl (ne_of_gt _)
    apply lt_of_lt_of_le EReal.bot_lt_zero
    apply EReal.const_le_limsup_forall
    intro n
    apply EReal.nneg_div
    apply log_one_le_iff.1
    simp only [Nat.one_le_ofNat]
  . apply Or.inr
    apply ne_of_gt
    apply lt_of_lt_of_le EReal.bot_lt_zero
    rw [← @Filter.limsup_const EReal ℕ _ Filter.atTop _ 0]
    apply EReal.const_le_limsup_forall
    intro n
    simp only [Filter.limsup_const]
    apply EReal.nneg_div
    specialize nneg_log_max n
    exact nneg_log_max

theorem entropy'_union [UniformSpace X] (T : X → X) (F G : Set X) :
    Entropy' T (F ∪ G) = max (Entropy' T F) (Entropy' T G) := by
  sorry
-/

end EntropyUnion

#lint
