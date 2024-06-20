/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import BET.TopologicalEntropy.Miscellaneous.Misc
import BET.TopologicalEntropy.Miscellaneous.ENNRealLog
import BET.TopologicalEntropy.Miscellaneous.ERealDiv
import BET.TopologicalEntropy.Miscellaneous.ERealMulCont
import BET.TopologicalEntropy.InvariantSubset
import BET.TopologicalEntropy.DynamicalUniformity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.UniformSpace.Basic

/-!
# Topological entropy via covers
We implement Bowen-Dinaburg's definitions of the topological entropy, via covers.

All is stated in the vocabulary of uniform spaces. For compact spaces, the uniform structure
is canonical, so the topological entropy depends only on the topological structure. This gives
a clean proof that the topological entropy is a topological invariant of the dynamics.

A notable choice is that we define the topological entropy of a subset of the whole space. Usually,
one defined the entropy of an invariant subset `F` as the entropy of the restriction of the
transformation to `F`. However, it is quite painful to work with subtypes and transport
all the necessary information (e.g. a nice description of the topology) to them. The current
version gives a meaning to the topological entropy of a subsystem, and a single lemma
(theorem `subset_restriction_entropy` in `.Systems.Morphism`) will give the equivalence between
both versions.

Another choice is to give a meaning to the entropy of `∅` (it must be `-∞` to stay coherent)
and to keep the possibility for the entropy to be infinite. Hence, the entropy takes values
in the extended reals `[-∞, +∞]`. The consequence is that we use many somewhat unusual
structures : `ENat`, `ENNReal`, `EReal`. The libraries of `ENat` and `EReal` are quite poor,
which in the case of `EReal` is quite annoying and explain the many additional files. In
addition, the handling of coercions can be quite bothersome, although never as much as with
Lean3.

Finally, I decided to work with minimal hypotheses. In particular, I did not implement a
"topological dynamical system" structure, but tried to keep the hypotheses as sharp as possible
at each point. I thus needed to handle many special cases, but some results are surprisingly
general.

TODO: Check the vocabulary. I introduced `IsDynamicalCoverOf`, `Mincard`, `CoverEntropy`/
`CoverEntropy'` (depending on whether one uses a `liminf` or a `limsup`), `Entropy`/`Entropy'`.
I am not convinced these are the right choices. For instance, I've already encountered `Minspan`
instead of `Mincard`. More importantly, having only `Entropy` as the final object
is somewhat too short: it does not differentiate between the cover or net versions,
which makes some statements ambiguous (and requires some care in the opening/closing
of namespaces).

TODO: The most painful part of the manipulation of topological entropy is going from `Mincard` to
`CoverEntropy`/`CoverEntropy'`: it involves a logarithm, a division, a `liminf`/`limsup`, and
multiple coercions. It is not helped by the weakness of the libraries on `liminf`/`limsup`.
I have not managed to write sensible proofs. Some clean-up would be welcome, although I think that
the best thing to do would be to write a file on "exponential growth" to make a clean passage
from estimates on `Mincard` to estimates on `CoverEntropy`/`CoverEntropy'`.
-/

namespace DynamicalCover

open InvariantSubset DynamicalUniformity UniformSpace

variable {X : Type _}

/-- Given a uniform neighborhood U, an integer n and a subset F, a subset s is a (n, U)-cover
(i.e. a refined cover) of F if any orbit of length n in F is U-shadowed by an orbit of length n
of a point in s.--/
def IsDynamicalCoverOf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
  F ⊆ ⋃ x : s, ball x (DynamicalUni T U n)

theorem dyncover_monotone_time {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ}
    (m_le_n : m ≤ n) {s : Set X} (h : IsDynamicalCoverOf T F U n s) :
    IsDynamicalCoverOf T F U m s := by
  apply @Set.Subset.trans X F _ (⋃ x : s, ball x (DynamicalUni T U m)) h
  apply Set.iUnion_mono
  intro x
  exact ball_mono (dynamical_uni_antitone_time T U m_le_n) x

theorem dyncover_antitone_uni {T : X → X} {F : Set X} {U V : Set (X × X)} (U_sub_V : U ⊆ V)
    {n : ℕ} {s : Set X} (h : IsDynamicalCoverOf T F U n s) :
    IsDynamicalCoverOf T F V n s := by
  apply @Set.Subset.trans X F _ (⋃ x : s, ball x (DynamicalUni T V n)) h
  apply Set.iUnion_mono
  intro x
  exact ball_mono (dynamical_uni_monotone_uni T n U_sub_V) x

theorem dyncover_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} :
    IsDynamicalCoverOf T ∅ U n ∅ := by
  simp only [IsDynamicalCoverOf, Set.empty_subset]

theorem dyncover_of_nonempty {T : X → X} {F : Set X} (h : F.Nonempty) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h' : IsDynamicalCoverOf T F U n s) :
    s.Nonempty := by
  cases' Set.nonempty_iUnion.1 (Set.Nonempty.mono h' h) with x hx
  use x
  exact Subtype.coe_prop x

theorem dyncover_time_zero (T : X → X) (F : Set X) (U : Set (X × X)) {s : Set X} (h : s.Nonempty) :
    IsDynamicalCoverOf T F U 0 s := by
  simp only [IsDynamicalCoverOf, ball, DynamicalUni, not_lt_zero', Function.iterate_prod_map,
    Set.iInter_of_empty, Set.iInter_univ, Set.preimage_univ, Set.iUnion_coe_set]
  cases' h with x x_in_s
  apply Set.subset_iUnion_of_subset x
  exact Set.subset_iUnion_of_subset x_in_s (Set.subset_univ F)

theorem dyncover_by_univ (T : X → X) (F : Set X) (n : ℕ) {s : Set X} (h : s.Nonempty) :
    IsDynamicalCoverOf T F Set.univ n s := by
  simp only [IsDynamicalCoverOf, ball, DynamicalUni, Function.iterate_prod_map, Set.preimage_univ,
    Set.iInter_univ, Set.iUnion_coe_set]
  cases' h with x x_in_s
  apply Set.subset_iUnion_of_subset x
  exact Set.subset_iUnion_of_subset x_in_s (Set.subset_univ F)

theorem dyncover_iterate {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {V : Set (X × X)}
    (V_symm : SymmetricRel V) {m : ℕ} (n : ℕ) {s : Finset X} (h : IsDynamicalCoverOf T F V m s) :
    ∃ t : Finset X, IsDynamicalCoverOf T F (compRel V V) (m * n) t ∧ t.card ≤ s.card ^ n := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · use ∅; clear h V_symm F_inv
    simp only [Finset.coe_empty, dyncover_of_empty, Finset.card_empty, zero_le, and_self]
  have _ : Nonempty X :=
    Set.nonempty_iff_univ_nonempty.2 (Set.Nonempty.mono (Set.subset_univ F) F_nonempty)
  have s_nonempty := dyncover_of_nonempty F_nonempty h
  cases' F_nonempty with x x_in_F
  rcases m.eq_zero_or_pos with (rfl | m_pos)
  · use {x}
    simp only [zero_mul, Finset.coe_singleton, Finset.card_singleton]
    constructor
    · exact dyncover_time_zero T F (compRel V V) (Set.singleton_nonempty x)
    · have := Nat.one_le_of_lt (Finset.Nonempty.card_pos s_nonempty)
      exact one_le_pow_of_one_le' this n
  have :
    ∀ β : Fin n → s, ∃ y : X,
      (⋂ k : Fin n, T^[m * k] ⁻¹' ball (β k) (DynamicalUni T V m)) ⊆
      ball y (DynamicalUni T (compRel V V) (m * n)) := by
    intro t
    by_cases inter_nonempty :
      (⋂ k : Fin n, T^[m * k] ⁻¹' ball (t k) (DynamicalUni T V m)).Nonempty
    . cases' inter_nonempty with y y_in_inter
      use y
      intro z z_in_inter
      simp only [ball, DynamicalUni, Function.iterate_prod_map, Set.mem_preimage, Set.mem_iInter,
        Prod_map, mem_compRel]
      simp only [ball, DynamicalUni, Function.iterate_prod_map, Set.mem_iInter, Set.mem_preimage,
        Prod_map, Subtype.forall, Finset.mem_range] at z_in_inter
      intro k k_lt_mn
      have kdivm_lt_n : k / m < n := Nat.div_lt_of_lt_mul k_lt_mn
      specialize z_in_inter ⟨(k / m), kdivm_lt_n⟩ (k % m) (Nat.mod_lt k m_pos)
      rw [← Function.iterate_add_apply T (k % m) (m * (k / m)), Nat.mod_add_div k m] at z_in_inter
      simp only [ball, DynamicalUni, Function.iterate_prod_map, Set.mem_iInter, Set.mem_preimage,
        Prod_map, Subtype.forall, Finset.mem_range] at y_in_inter
      specialize y_in_inter ⟨(k / m), kdivm_lt_n⟩ (k % m) (Nat.mod_lt k m_pos)
      rw [← Function.iterate_add_apply T (k % m) (m * (k / m)), Nat.mod_add_div k m] at y_in_inter
      exact mem_comp_of_mem_ball V_symm y_in_inter z_in_inter
    · rw [Set.not_nonempty_iff_eq_empty] at inter_nonempty
      rw [inter_nonempty]
      use x
      exact Set.empty_subset _
  choose! dynamical_cover h_dynamical_cover using this
  classical
  let sn := Set.range dynamical_cover
  have _ := Set.fintypeRange dynamical_cover
  use sn.toFinset
  constructor
  · intro y y_in_F
    have key : ∀ k : Fin n, ∃ z : s, y ∈ T^[m * k] ⁻¹' ball z (DynamicalUni T V m) := by
      intro k
      have := h (iter_of_inv_in_inv' F_inv (m * k) y_in_F)
      simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop] at this
      rcases this with ⟨z, ⟨z_in_s, hz⟩⟩
      use ⟨z, z_in_s⟩
      exact hz
    rw [Finset.coe_nonempty] at s_nonempty
    have _ : Nonempty s := Finset.Nonempty.coe_sort s_nonempty
    choose! t ht using key
    specialize h_dynamical_cover t
    simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, Set.toFinset_range,
      Finset.mem_image, Finset.mem_univ, true_and, exists_prop, exists_exists_eq_and, sn]
    simp only [Set.mem_preimage, Subtype.forall, Finset.mem_range] at ht
    use t
    apply h_dynamical_cover
    simp only [Set.mem_iInter, Set.mem_preimage, Subtype.forall, Finset.mem_range]
    exact ht
  · rw [Set.toFinset_card]
    apply le_trans (Fintype.card_range_le dynamical_cover)
    simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, le_refl]

theorem dyncover_iterate' {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {V : Set (X × X)}
    (V_symm : SymmetricRel V) {m : ℕ} (m_pos : 0 < m) (n : ℕ) {s : Finset X}
    (h : IsDynamicalCoverOf T F V m s) :
    ∃ t : Finset X, IsDynamicalCoverOf T F (compRel V V) n t ∧ t.card ≤ s.card ^ (n / m + 1) := by
  cases' dyncover_iterate F_inv V_symm (n / m + 1) h with t ht
  use t
  exact ⟨dyncover_monotone_time (le_of_lt (Nat.lt_mul_div_succ n m_pos)) ht.1, ht.2⟩

/-- We can always find a (n, U)-refined cover of a compact subspace.
If `T` is assumed continuous, this statement can be proved quickly by covering `F`
by refined subsets, which are in this case open, and extracting a finite subcover.
We bypass this condition, using the comparatively complex lemma `dyncover_iterate`.-/
theorem exists_dyncover_of_compact_inv [UniformSpace X] {T : X → X} {F : Set X}
    (F_inv : IsInvariant T F) (F_compact : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X)
    (n : ℕ) :
    ∃ s : Finset X, IsDynamicalCoverOf T F U n s := by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, ⟨V_symm, V_comp_U⟩⟩
  let open_cover := fun x : X ↦ ball x V
  have := IsCompact.elim_nhds_subcover F_compact open_cover (fun (x : X) _ ↦ ball_mem_nhds x V_uni)
  rcases this with ⟨s, _, s_cover⟩
  have : IsDynamicalCoverOf T F V 1 s := by
    intro x x_in_F
    specialize s_cover x_in_F
    simp only [Set.mem_iUnion, exists_prop] at s_cover
    rcases s_cover with ⟨y, y_in_s, x_in_By⟩
    simp only [Finset.coe_sort_coe, DynamicalUni, Nat.lt_one_iff, Function.iterate_prod_map,
      Set.iInter_iInter_eq_left, Function.iterate_zero, Prod.map_id, Set.preimage_id_eq, id_eq,
      Set.mem_iUnion, Subtype.exists, exists_prop]
    use y, y_in_s
  rcases dyncover_iterate F_inv V_symm n this with ⟨t, t_dynamical_cover, t_card⟩
  rw [one_mul n] at t_dynamical_cover
  use t
  exact dyncover_antitone_uni V_comp_U t_dynamical_cover

/-- The smallest cardinal of a (n,U)-refined cover of F. Takes values in ℕ∞, and is infinite
if and only if F admits no finite refined cover.--/
noncomputable def Mincard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨅ (s : Finset X) (_ : IsDynamicalCoverOf T F U n s), (s.card : ℕ∞)

theorem mincard_eq_sInf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Mincard T F U n
    = sInf (WithTop.some '' (Finset.card '' {s : Finset X | IsDynamicalCoverOf T F U n s})) := by
  unfold Mincard
  rw [← Set.image_comp, sInf_image]
  simp only [Set.mem_setOf_eq, ENat.some_eq_coe, Function.comp_apply]

theorem mincard_le_card {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynamicalCoverOf T F U n s) :
    Mincard T F U n ≤ s.card :=
  @iInf₂_le ℕ∞ (Finset X) _ _ _ s h

theorem finite_mincard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Mincard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynamicalCoverOf T F U n s ∧ (s.card : ℕ∞) = Mincard T F U n := by
  constructor
  · rw [mincard_eq_sInf T F U n]
    intro finite_mincard
    rcases WithTop.ne_top_iff_exists.1 (ne_of_lt finite_mincard) with ⟨k, k_mincard⟩
    rw [← k_mincard]
    have h_nemp : Set.Nonempty (Finset.card '' {s : Finset X | IsDynamicalCoverOf T F U n s}) := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      simp only [ENat.some_eq_coe, h, Set.image_empty, sInf_empty, lt_self_iff_false]
        at finite_mincard
    have h_bddb : BddBelow (Finset.card '' {s : Finset X | IsDynamicalCoverOf T F U n s}) := by
      use 0
      simp only [lowerBounds, Set.mem_setOf_eq, zero_le, implies_true]
    rw [← WithTop.coe_sInf' h_nemp h_bddb] at k_mincard
    norm_cast at k_mincard
    have key := Nat.sInf_mem h_nemp
    rw [← k_mincard] at key
    simp only [Set.mem_image, Set.mem_setOf_eq] at key
    simp only [ENat.some_eq_coe, Nat.cast_inj]
    exact key
  · rintro ⟨s, ⟨_, s_mincard⟩⟩
    rw [← s_mincard]
    exact WithTop.coe_lt_top s.card

theorem finite_mincard_of_compact [UniformSpace X] {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    (F_compact : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    ∃ s : Finset X, IsDynamicalCoverOf T F U n s ∧ (s.card : ℕ∞) = Mincard T F U n := by
  rw [← finite_mincard_iff T F U n]
  rcases exists_dyncover_of_compact_inv F_inv F_compact U_uni n with ⟨s, s_cover⟩
  exact lt_of_le_of_lt (mincard_le_card s_cover) (WithTop.coe_lt_top s.card)

theorem cover_elim {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynamicalCoverOf T F U n s) :
    ∃ t : Finset X, IsDynamicalCoverOf T F U n t ∧ t.card ≤ s.card
    ∧ ∀ x ∈ t, ((ball x (DynamicalUni T U n)) ∩ F).Nonempty := by
  classical
  use Finset.filter (fun x : X => ((ball x (DynamicalUni T U n)) ∩ F).Nonempty) s
  simp only [Finset.coe_filter, Finset.mem_filter, and_imp, imp_self, implies_true, and_true]
  constructor
  . intros y y_in_F
    specialize h y_in_F
    simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop] at h
    rcases h with ⟨z, z_in_s, y_in_Bz⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
    use z
    exact ⟨⟨z_in_s, Set.nonempty_of_mem ⟨y_in_Bz, y_in_F⟩⟩, y_in_Bz⟩
  . exact Finset.card_mono (Finset.filter_subset _ s)

theorem minimal_cover_balls_inter {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : (s.card : ℕ∞) = Mincard T F U n) (h' : IsDynamicalCoverOf T F U n s) :
    ∀ x ∈ s, (F ∩ ball x (DynamicalUni T U n)).Nonempty := by
  classical
  by_contra hypo
  push_neg at hypo
  rcases hypo with ⟨x, x_in_s, empty_ball⟩
  let t := Finset.erase s x
  have t_smaller_cover : IsDynamicalCoverOf T F U n t := by
    intro y y_in_F
    specialize h' y_in_F
    simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop] at h'
    rcases h' with ⟨z, hz⟩
    simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, Finset.mem_erase, ne_eq,
      exists_prop, t]
    use z
    split_ands
    . intro z_eq_x
      rw [z_eq_x] at hz
      apply Set.not_mem_empty y
      rw [← empty_ball]
      exact Set.mem_inter y_in_F hz.2
    . exact hz.1
    . exact hz.2
  apply not_lt_of_le ( mincard_le_card t_smaller_cover)
  rw [← h]
  norm_cast
  exact Finset.card_erase_lt_of_mem x_in_s

theorem mincard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ Mincard T F U n) := by
  intros m n m_le_n
  simp only
  rw [mincard_eq_sInf T F U n, mincard_eq_sInf T F U m]
  apply sInf_le_sInf
  apply Set.image_subset
  apply Set.image_subset
  rw [Set.setOf_subset_setOf]
  intro s
  exact dyncover_monotone_time m_le_n

theorem mincard_antitone_uni (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X×X) ↦ Mincard T F U n) := by
  intros U V U_sub_V
  simp only
  rw [mincard_eq_sInf T F U n, mincard_eq_sInf T F V n]
  apply sInf_le_sInf
  apply Set.image_subset
  apply Set.image_subset
  rw [Set.setOf_subset_setOf]
  intro s
  exact dyncover_antitone_uni U_sub_V

@[simp]
theorem mincard_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} : Mincard T ∅ U n = 0 := by
  apply le_antisymm
  · apply @sInf_le ℕ∞ _
    use ∅
    simp only [IsDynamicalCoverOf, Finset.coe_sort_coe, Set.iUnion_of_empty, Set.empty_subset,
      Finset.card_empty, CharP.cast_eq_zero, iInf_pos]
  · exact zero_le (Mincard T ∅ U n)

theorem empty_iff_mincard_zero (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    F = ∅ ↔ Mincard T F U n = 0 := by
  apply Iff.intro
  · intro F_empty
    rw [F_empty]
    exact mincard_of_empty
  · intro zero_cover
    have := finite_mincard_iff T F U n
    rw [zero_cover] at this
    simp only [ENat.zero_lt_top, IsDynamicalCoverOf, Finset.coe_sort_coe, Nat.cast_eq_zero,
      Finset.card_eq_zero, exists_eq_right, Set.iUnion_of_empty, true_iff] at this
    exact Set.eq_empty_iff_forall_not_mem.2 this

theorem pos_mincard_of_nonempty (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    F.Nonempty ↔ 1 ≤ Mincard T F U n := by
  rw [ENat.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty, not_iff_not]
  exact empty_iff_mincard_zero T F U n

theorem mincard_time_zero_of_nonempty (T : X → X) {F : Set X} (F_nonempty : F.Nonempty) (U : Set (X × X)) :
    Mincard T F U 0 = 1 := by
  cases' F_nonempty with x x_in_F
  apply le_antisymm
  · have key := (dyncover_time_zero T F U (Set.singleton_nonempty x))
    rw [← Finset.coe_singleton] at key
    apply le_of_le_of_eq (mincard_le_card key)
    rw [Finset.card_singleton, Nat.cast_one]
  · apply le_iInf₂
    intro s s_cover
    norm_cast
    apply Finset.Nonempty.card_pos
    rcases Set.mem_iUnion.1 (s_cover x_in_F) with ⟨⟨y, y_in_s⟩, _⟩
    norm_cast at y_in_s
    use y

theorem mincard_time_zero_le (T : X → X) (F : Set X) (U : Set (X × X)) :
    Mincard T F U 0 ≤ 1 := by
  rcases Set.eq_empty_or_nonempty F with (rfl | F_nemp)
  . rw [mincard_of_empty]
    exact zero_le_one
  . rw [mincard_time_zero_of_nonempty T F_nemp U]

theorem mincard_by_univ_of_nonempty (T : X → X) {F : Set X} (F_nonempty : F.Nonempty) (n : ℕ) :
    Mincard T F Set.univ n = 1 := by
  cases' F_nonempty with x x_in_F
  apply le_antisymm
  · have := (dyncover_by_univ T F n (Set.singleton_nonempty x))
    rw [← Finset.coe_singleton] at this
    apply le_of_le_of_eq (mincard_le_card this)
    rw [Finset.card_singleton, Nat.cast_one]
  · apply le_iInf₂
    intro s s_cover
    norm_cast
    apply Finset.Nonempty.card_pos
    rcases Set.mem_iUnion.1 (s_cover x_in_F) with ⟨⟨y, y_in_s⟩, _⟩
    norm_cast at y_in_s
    use y

theorem mincard_by_univ_le (T : X → X) (F : Set X) (n : ℕ) :
    Mincard T F Set.univ n ≤ 1 := by
  rcases Set.eq_empty_or_nonempty F with (rfl | F_nemp)
  . rw [mincard_of_empty]
    exact zero_le_one
  . rw [mincard_by_univ_of_nonempty T F_nemp n]

theorem mincard_exponential_bound {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    {V : Set (X × X)} (V_symm : SymmetricRel V) (m n : ℕ) :
    Mincard T F (compRel V V) (m * n) ≤ Mincard T F V m ^ n := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · rw [mincard_of_empty]; exact zero_le _
  rcases n.eq_zero_or_pos with (rfl | n_pos)
  · rw [mul_zero, mincard_time_zero_of_nonempty T F_nonempty (compRel V V), pow_zero]
  by_cases h : Mincard T F V m = ⊤
  · rw [h]
    exact le_of_le_of_eq (@le_top ℕ∞ _ _ _) (Eq.symm (Misc.ENat.top_pow n_pos))
  · replace h := lt_top_iff_ne_top.2 h
    rcases (finite_mincard_iff T F V m).1 h with ⟨s, ⟨s_cover, s_mincard⟩⟩
    rcases dyncover_iterate F_inv V_symm n s_cover with ⟨t, ⟨t_cover, t_le_sn⟩⟩
    rw [← s_mincard]
    exact le_trans (mincard_le_card t_cover) (WithTop.coe_le_coe.2 t_le_sn)

theorem exponential_bound' {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {V : Set (X × X)}
    (V_symm : SymmetricRel V) {m : ℕ} (m_pos : 0 < m) (n : ℕ) :
    Mincard T F (compRel V V) n ≤ Mincard T F V m ^ (n / m + 1) := by
  apply le_trans _ (mincard_exponential_bound F_inv V_symm m (n / m + 1))
  exact mincard_monotone_time T F (compRel V V) (le_of_lt (Nat.lt_mul_div_succ n m_pos))


open ENNReal ERealDiv

theorem log_mincard_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} :
    log (Mincard T ∅ U n) = ⊥ := by
  rw [mincard_of_empty, ENat.toENNReal_zero, log_zero]

theorem nneg_log_mincard_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X))
    (n : ℕ) :
    0 ≤ log (Mincard T F U n) := by
  apply log_one_le_iff.1
  rw [← ENat.toENNReal_one, ENat.toENNReal_le]
  exact (pos_mincard_of_nonempty T F U n).1 h

theorem log_mincard_upper_bound {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {V : Set (X × X)}
    (V_symm : SymmetricRel V) (m n : ℕ) :
    log (Mincard T F (compRel V V) (m * n)) / (n : ENNReal) ≤
    log (Mincard T F V m) := by
  rcases n.eq_zero_or_pos with (rfl | n_pos)
  · rw [mul_zero, CharP.cast_eq_zero]
    rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
    · simp only [mincard_of_empty, ENat.toENNReal_zero, log_zero, le_bot_iff]
      exact EReal.bot_div_ntop ENNReal.zero_ne_top
    · rw [mincard_time_zero_of_nonempty T F_nonempty (compRel V V), ENat.toENNReal_one, log_one,
        EReal.zero_div]
      apply log_one_le_iff.1
      rw [← ENat.toENNReal_one, ENat.toENNReal_le]
      exact (pos_mincard_of_nonempty T F V m).1 F_nonempty
  · apply (@EReal.div_le_iff_le_mul _ _ n _ _).2
    · rw [← log_pow, ← log_le_iff_le]
      nth_rw 2 [← ENat.toENNRealRingHom_apply]
      rw [← RingHom.map_pow ENat.toENNRealRingHom _ n, ENat.toENNRealRingHom_apply,
        ENat.toENNReal_le]
      exact mincard_exponential_bound F_inv V_symm m n
    · norm_cast
      exact Ne.symm (ne_of_lt n_pos)
    · simp only [ne_eq, natCast_ne_top, not_false_eq_true]

theorem log_mincard_upper_bound' {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    {V : Set (X × X)} (V_symm : SymmetricRel V) {m : ℕ} (m_pos : 0 < m) (n : ℕ) :
    log (Mincard T F (compRel V V) n) / (n : ENNReal) ≤
    log (Mincard T F V m) / (m : ENNReal) * (m / n + 1 : ENNReal) := by
  have m_ne_top : (m : ENNReal) ≠ ⊤ := by simp only [ne_eq, natCast_ne_top, not_false_eq_true]
  have n_ne_top : (n : ENNReal) ≠ ⊤ := by simp only [ne_eq, natCast_ne_top, not_false_eq_true]
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · simp only [mincard_of_empty, ENat.toENNReal_zero, log_zero, EReal.bot_div_ntop n_ne_top,
    EReal.coe_ennreal_add, EReal.coe_ennreal_one, bot_le]
  rcases n.eq_zero_or_pos with (rfl | n_pos)
  · rw [mincard_time_zero_of_nonempty T F_nonempty (compRel V V), ENat.toENNReal_one, log_one,
      EReal.zero_div]
    apply mul_nonneg
    · apply EReal.nneg_div
      rw [← log_one_le_iff, ← ENat.toENNReal_one, ENat.toENNReal_le]
      exact (pos_mincard_of_nonempty T F V m).1 F_nonempty
    · exact EReal.coe_ennreal_nonneg _
  have n_ne_zero : (n : ENNReal) ≠ 0 := by exact_mod_cast n_pos.ne.symm
  have m_ne_zero : (m : ENNReal) ≠ 0 := by exact_mod_cast m_pos.ne.symm
  rw [EReal.div_le_iff_le_mul n_ne_zero n_ne_top, mul_comm, mul_assoc, EReal.mul_div_right,
    EReal.le_div_iff_mul_le m_ne_zero m_ne_top, ← EReal.coe_ennreal_mul, add_mul,
    ENNReal.div_mul_cancel n_ne_zero n_ne_top, one_mul, mul_comm, mul_comm _ (ENNReal.toEReal _)]
  norm_cast
  repeat' rw [← log_pow]
  apply log_monotone
  rw [← ENat.toENNRealRingHom_apply, ← RingHom.map_pow ENat.toENNRealRingHom _ m, ←
    RingHom.map_pow ENat.toENNRealRingHom _ (m + n), ENat.toENNRealRingHom_apply, ENat.toENNReal_le]
  have key := mincard_monotone_time T F (compRel V V)
    (le_of_lt (Nat.lt_mul_div_succ n m_pos))
  have lock := mincard_exponential_bound F_inv V_symm m (n / m + 1)
  replace key := le_trans key lock; clear lock
  replace key := @pow_le_pow_left ℕ∞ _ _ _ bot_le key m
  apply le_trans key; clear key
  rw [← pow_mul]
  apply pow_le_pow_right _ _
  · exact (pos_mincard_of_nonempty T F V m).1 F_nonempty
  · rw [mul_comm, mul_add, mul_one, add_comm m n]
    exact add_le_add_right (Nat.mul_div_le n m) m

open ENNReal ERealDiv

/-- The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the
size of the smallest (n, U)-refined cover of F. Takes values in the space fo extended real numbers
[-∞,+∞]. The first version uses a liminf.--/
noncomputable def CoverEntropy {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.liminf fun n : ℕ ↦ log (Mincard T F U n) / (n : ENNReal)

/-- The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the
size of the smallest (n, U)-refined cover of F. Takes values in the space fo extended real numbers
[-∞,+∞]. The second version uses a limsup.--/
noncomputable def CoverEntropy' {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.limsup fun n : ℕ ↦ log (Mincard T F U n) / (n : ENNReal)

theorem cover_entropy_antitone_uni {X : Type _} (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X×X) ↦ CoverEntropy T F U) := by
  intro U V U_sub_V
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono n
  apply log_monotone
  apply ENat.toENNReal_mono
  exact mincard_antitone_uni T F n U_sub_V

theorem cover_entropy'_antitone_uni {X : Type _} (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X×X) ↦ CoverEntropy' T F U) := by
  intro U V U_sub_V
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono n
  apply log_monotone
  apply ENat.toENNReal_mono
  exact mincard_antitone_uni T F n U_sub_V

theorem cover_entropy_le' {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X)) :
    CoverEntropy T F U ≤ CoverEntropy' T F U :=
  Filter.liminf_le_limsup

@[simp]
theorem cover_entropy'_of_empty {X : Type _} {T : X → X} {U : Set (X × X)} :
    CoverEntropy' T ∅ U = ⊥ := by
  suffices h : (fun n : ℕ ↦ log (Mincard T ∅ U n) / (n : ENNReal)) = (fun n : ℕ ↦ ⊥)
  · unfold CoverEntropy'
    rw [h]
    exact Filter.limsup_const ⊥
  · ext1 n
    rw [log_mincard_of_empty]
    apply EReal.bot_div_ntop
    simp only [ne_eq, natCast_ne_top, not_false_eq_true]

@[simp]
theorem cover_entropy_of_empty {X : Type _} {T : X → X} {U : Set (X × X)} :
    CoverEntropy T ∅ U = ⊥ := by
  rw [← le_bot_iff]
  exact le_of_le_of_eq (cover_entropy_le' T ∅ U) cover_entropy'_of_empty

theorem nneg_cover_entropy_of_nonempty {X : Type _} (T : X → X) {F : Set X}
    (F_nonempty : F.Nonempty) (U : Set (X × X)) :
    0 ≤ CoverEntropy T F U := by
  apply le_trans _ Filter.iInf_le_liminf
  apply le_iInf _
  intro n
  exact EReal.nneg_div (nneg_log_mincard_of_nonempty T F_nonempty U n)

theorem nneg_cover_entropy'_of_nonempty {X : Type _} (T : X → X) {F : Set X}
    (F_nonempty : F.Nonempty) (U : Set (X × X)) :
    0 ≤ CoverEntropy' T F U :=
  le_trans (nneg_cover_entropy_of_nonempty T F_nonempty U) (cover_entropy_le' T F U)

theorem cover_entropy_by_univ_of_nonempty (T : X → X) {F : Set X} (F_nonempty : F.Nonempty) :
    CoverEntropy T F Set.univ = 0 := by
  simp only [CoverEntropy, mincard_by_univ_of_nonempty T F_nonempty, ENat.toENNReal_one, log_one,
    EReal.zero_div, Filter.liminf_const]

theorem cover_entropy'_by_univ_of_nonempty (T : X → X) {F : Set X} (F_nonempty : F.Nonempty) :
    CoverEntropy' T F Set.univ = 0 := by
  simp only [CoverEntropy', mincard_by_univ_of_nonempty T F_nonempty, ENat.toENNReal_one, log_one,
    EReal.zero_div, Filter.limsup_const]

theorem cover_entropy_le_log_mincard_div {X : Type _} {T : X → X} {F : Set X}
    (F_inv : IsInvariant T F) {V : Set (X × X)} (V_symm : SymmetricRel V) {n : ℕ} (n_pos : 0 < n) :
    CoverEntropy T F (compRel V V) ≤ log (Mincard T F V n) / (n : ENNReal) := by
  apply Filter.liminf_le_of_frequently_le' _
  rw [Filter.frequently_atTop]
  intro N
  use N * n
  constructor
  . have := Nat.mul_le_mul_left N (Nat.one_le_of_lt n_pos)
    rw [mul_one N] at this
    exact this
  . have key := log_mincard_upper_bound F_inv V_symm n N
    rw [mul_comm n N] at key
    replace key := EReal.div_left_mono' n key
    rw [EReal.div_mul _ _] at key
    . simp only [Nat.cast_mul, ge_iff_le]
      exact key
    . simp only [ne_eq, Nat.cast_eq_zero, natCast_ne_top, not_false_eq_true, or_true]
    . simp only [ne_eq, natCast_ne_top, not_false_eq_true, Nat.cast_eq_zero, true_or]

theorem cover_entropy_le_card_div {X : Type _} {T : X → X} {F : Set X}
    (F_inv : IsInvariant T F) {V : Set (X × X)} (V_symm : SymmetricRel V)
    {n : ℕ} (n_pos : 0 < n) {s : Finset X} (h : IsDynamicalCoverOf T F V n s) :
    CoverEntropy T F (compRel V V) ≤ log s.card / (n : ENNReal) := by
  apply le_trans (cover_entropy_le_log_mincard_div F_inv V_symm n_pos)
  apply EReal.div_left_mono
  apply log_monotone
  norm_cast
  exact mincard_le_card h

lemma intermediate_lemma (a : EReal) (m : ℕ) :
    Filter.Tendsto (fun (n : ℕ) ↦ a * (m / n + 1 : ENNReal)) Filter.atTop (nhds a) := by
  have : (fun (n : ℕ) ↦ a * (m / n + 1 : ENNReal))
      = (fun p : EReal × EReal ↦ p.1 * p.2)
      ∘ (fun (n : ℕ) ↦ Prod.mk a ((m / n + 1 : ENNReal) : EReal)) := by
    ext n
    simp
  rw [this]; clear this
  have one_ne_top : (1 : EReal) ≠ ⊤ := by decide
  have key := ContinuousAt.tendsto <| @ERealMulCont.continuousAt_mul (a, 1)
    (Or.inr  WithBot.one_ne_bot) (Or.inr one_ne_top) (Or.inr one_ne_zero) (Or.inr one_ne_zero)
  simp only [mul_one] at key
  apply Filter.Tendsto.comp key; clear key one_ne_top
  rw [Prod.tendsto_iff]
  constructor; exact tendsto_const_nhds
  simp only [EReal.coe_ennreal_add, EReal.coe_ennreal_one]; clear a
  have limit_zero := @ENNReal.Tendsto.const_div ℕ Filter.atTop (fun (n : ℕ) ↦ (n : ENNReal))
    m ⊤ ENNReal.tendsto_nat_nhds_top (Or.inr <| ENNReal.natCast_ne_top m)
  simp only [div_top] at limit_zero
  have limit_one : Filter.Tendsto (fun (_ : ℕ) ↦ (1 : ENNReal)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have key := Filter.Tendsto.add limit_zero limit_one; clear limit_zero limit_one
  rw [zero_add] at key
  have : (fun (n : ℕ) ↦ ((m / n : ENNReal)+1 : EReal))
      = ENNReal.toEReal ∘ (fun (n : ℕ) ↦ (m / n + 1 : ENNReal)) := by
    ext n
    simp only [Function.comp_apply, EReal.coe_ennreal_add, EReal.coe_ennreal_one]
  rw [this]; clear this
  apply Filter.Tendsto.comp _ key
  exact ContinuousAt.tendsto (Continuous.continuousAt continuous_coe_ennreal_ereal)

theorem cover_entropy'_le_log_mincard_div {X : Type _} {T : X → X} {F : Set X}
    (F_inv : IsInvariant T F) {V : Set (X × X)} (V_symm : SymmetricRel V) {n : ℕ} (n_pos : 0 < n) :
    CoverEntropy' T F (compRel V V) ≤ log (Mincard T F V n) / (n : ENNReal) := by
  have upper_bound := log_mincard_upper_bound' F_inv V_symm n_pos
  replace upper_bound := @Filter.eventually_of_forall _ _ Filter.atTop upper_bound
  apply le_trans (Misc.EReal_limsup_le_limsup upper_bound); clear upper_bound
  apply le_of_eq
  apply Filter.Tendsto.limsup_eq
  exact intermediate_lemma (log (Mincard T F V n) / (n : ENNReal)) n

theorem cover_entropy'_le {X : Type _} {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    {V : Set (X × X)} (V_symm : SymmetricRel V) :
    CoverEntropy' T F (compRel V V) ≤ CoverEntropy T F V := by
  apply Filter.le_liminf_of_le
  . use ⊤
    simp only [ge_iff_le, Filter.eventually_map, Filter.eventually_atTop, le_top,
      forall_exists_index, implies_true, forall_const]
  . simp only [Filter.eventually_atTop, ge_iff_le]
    use 1
    intro m m_pos
    exact cover_entropy'_le_log_mincard_div F_inv V_symm m_pos

theorem finite_cover_entropy_of_compact {X : Type _} [UniformSpace X] {T : X → X} {F : Set X}
  (F_inv : IsInvariant T F) (F_compact : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) :
CoverEntropy T F U < ⊤ := by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, V_symm, V_comp_U⟩
  rcases finite_mincard_of_compact F_inv F_compact V_uni 1 with ⟨s, ⟨s_cover, _⟩⟩
  apply lt_of_le_of_lt (cover_entropy_antitone_uni T F V_comp_U)
  apply lt_of_le_of_lt (cover_entropy_le_card_div F_inv V_symm zero_lt_one s_cover)
  rw [Nat.cast_one, EReal.div_one, ← log_lt_top_iff]
  change ((Finset.card s : ENat) : ENNReal) < ⊤
  rw [← ENat.toENNReal_top, ENat.toENNReal_lt]
  exact Ne.lt_top (ENat.coe_ne_top (Finset.card s))

/-- The entropy of T restricted to F, obtained by taking the supremum over uniformity neighbourhoods.
Note that this supremum is approached by taking small neighbourhoods.--/
noncomputable def Entropy [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ (U : Set (X × X)) (_ : U ∈ 𝓤 X), CoverEntropy T F U

/-- An alternative definition of the entropy of T restricted to F, using a limsup instead of
a liminf.--/
noncomputable def Entropy' [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ (U : Set (X × X)) (_ : U ∈ 𝓤 X), CoverEntropy' T F U

theorem entropy_antitone_filter (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @Entropy X u T F := by
  intro u₁ u₂ h
  apply iSup₂_le
  intro U U_uni₂
  have := (Filter.le_def.1 h) U U_uni₂
  simp only at this
  apply le_iSup₂ U this

theorem entropy'_antitone_filter (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @Entropy' X u T F := by
  intro u₁ u₂ h
  apply iSup₂_le
  intro U U_uni₂
  have := (Filter.le_def.1 h) U U_uni₂
  simp only at this
  apply le_iSup₂ U this

variable [UniformSpace X]

theorem entropy_le_entropy' (T : X → X) (F : Set X) :
    Entropy T F ≤ Entropy' T F :=
  iSup₂_mono (fun (U : Set (X × X)) (_ : U ∈ uniformity X) ↦ cover_entropy_le' T F U)

theorem cover_entropy_le_entropy (T : X → X) (F : Set X) {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    CoverEntropy T F U ≤ Entropy T F := by
  apply le_trans _ (le_iSup _ U)
  simp only [h, iSup_pos, le_refl]

theorem cover_entropy'_le_entropy' (T : X → X) (F : Set X) {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    CoverEntropy' T F U ≤ Entropy' T F := by
  apply le_trans _ (le_iSup _ U)
  simp only [h, iSup_pos, le_refl]

@[simp]
theorem entropy_of_empty {T : X → X} : Entropy T ∅ = ⊥ := by
  simp only [Entropy, cover_entropy_of_empty, iSup_bot]

@[simp]
theorem entropy'_of_empty {T : X → X} : Entropy' T ∅ = ⊥ := by
  simp only [Entropy', cover_entropy'_of_empty, iSup_bot]

theorem nneg_entropy_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) : 0 ≤ Entropy T F := by
  apply le_iSup_of_le Set.univ
  simp only [Filter.univ_mem, iSup_pos]
  exact nneg_cover_entropy_of_nonempty T h Set.univ

theorem nneg_entropy'_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) : 0 ≤ Entropy' T F :=
  le_trans (nneg_entropy_of_nonempty T h) (entropy_le_entropy' T F)

theorem entropy_eq_entropy' (T : X → X) {F : Set X} (h : IsInvariant T F) :
    Entropy T F = Entropy' T F := by
  apply le_antisymm (entropy_le_entropy' T F)
  apply iSup₂_le; intros U U_uni
  rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
  apply le_trans (cover_entropy'_antitone_uni T F V_comp_U)
  apply le_iSup₂_of_le V V_uni
  exact cover_entropy'_le h V_symm

end DynamicalCover


#lint
