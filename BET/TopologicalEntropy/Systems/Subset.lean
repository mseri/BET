/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import BET.TopologicalEntropy.DynamicalNet

/-!
# Topological entropy of subsets: monotonicity, closure
Proof that the topological entropy depends monotonically on the subset. Main results
are `entropy_monotone_space₁`/`entropy'_monotone_space₁` (for the cover version)
and `entropy_monotone_space₂`/`entropy'_monotone_space₂` (for the net version). I have decided
to keep all the intermediate steps, since they may be useful in the study of other systems.

For uniformly continuous maps, proof that the entropy of a subset is the entropy of its closure.
Main results are `entropy_of_closure` and `entropy'_of_closure`.

TODO: I think one could implement a notion of Hausdorff onvergence for subsets using uniform
spaces, and then prove the semicontinuity of the topological entropy. It would be a nice
generalization of these lemmas on closures.
-/

namespace EntropyMonotoneSpace

open ERealDiv ENNReal DynamicalCover

variable {X : Type _}

theorem cover_of_monotone_space {T : X → X} {F G : Set X} (F_sub_G : F ⊆ G) {U : Set (X × X)}
    {n : ℕ} {s : Set X} (h : IsDynamicalCoverOf T G U n s) :
    IsDynamicalCoverOf T F U n s :=
  Set.Subset.trans F_sub_G h

theorem cover_mincard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone (fun F : Set X ↦ Mincard T F U n) := by
  intro F G F_sub_G
  simp only
  rw [mincard_eq_sInf T F U n, mincard_eq_sInf T G U n]
  apply sInf_le_sInf
  apply Set.image_mono
  apply Set.image_mono
  rw [Set.setOf_subset_setOf]
  intro _
  exact cover_of_monotone_space F_sub_G

theorem cover_entropy_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ CoverEntropy T F U) := by
  intro F G F_sub_G
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_monotone_space T U n F_sub_G

theorem cover_entropy'_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ CoverEntropy' T F U) := by
  intro F G F_sub_G
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_monotone_space T U n F_sub_G

theorem entropy_monotone_space₁ [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ Entropy T F) := by
  intro F G F_sub_G
  apply iSup₂_mono; intros U _
  exact cover_entropy_monotone_space T U F_sub_G

theorem entropy'_monotone_space₁ [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ Entropy' T F) := by
  intro F G F_sub_G
  apply iSup₂_mono; intros U _
  exact cover_entropy'_monotone_space T U F_sub_G

end EntropyMonotoneSpace

namespace EntropyMonotoneSpace

open ERealDiv ENNReal DynamicalNet

variable {X : Type _}

theorem net_of_monotone_space {T : X → X} {F G : Set X} (F_sub_G : F ⊆ G ) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynamicalNetOf T F U n s) :
    IsDynamicalNetOf T G U n s :=
  ⟨Set.Subset.trans h.1 F_sub_G, h.2⟩

theorem net_maxcard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone (fun F : Set X ↦ Maxcard T F U n) := by
  intro F G F_sub_G
  simp only
  rw [maxcard_eq_sSup T F U n, maxcard_eq_sSup T G U n]
  apply sSup_le_sSup
  apply Set.image_mono
  apply Set.image_mono
  rw [Set.setOf_subset_setOf]
  intro _
  exact net_of_monotone_space F_sub_G

theorem net_entropy_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ NetEntropy T F U) := by
  intros F G F_sub_G
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact net_maxcard_monotone_space T U n F_sub_G

theorem net_entropy'_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ NetEntropy' T F U) := by
  intros F G F_sub_G
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact net_maxcard_monotone_space T U n F_sub_G

theorem entropy_monotone_space₂ [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ Entropy T F) := by
  intros F G F_sub_G
  apply iSup₂_mono; intros U _
  exact net_entropy_monotone_space T U F_sub_G

theorem entropy'_monotone_space₂ [UniformSpace X] (T : X → X)  :
    Monotone (fun F : Set X ↦ Entropy' T F) := by
  intros F G F_sub_G
  apply iSup₂_mono; intros U _
  exact net_entropy'_monotone_space T U F_sub_G

end EntropyMonotoneSpace


namespace EntropyClosure

open Function UniformSpace ERealDiv ENNReal DynamicalCover DynamicalUniformity

variable {X : Type _} [UniformSpace X] {T : X → X} (h : UniformContinuous T)

theorem dyncover_of_closure {F : Set X} {U V : Set (X × X)} (V_uni : V ∈ 𝓤 X) {n : ℕ} {s : Set X}
    (s_cover : IsDynamicalCoverOf T F U n s) :
    IsDynamicalCoverOf T (closure F) (compRel U V) n s := by
  /-WLOG, the uniformity V can be assumed symmetric.-/
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_sub_V⟩
  rw [id_eq] at W_sub_V
  apply dyncover_antitone_uni (compRel_mono (Set.Subset.refl U) W_sub_V); clear W_sub_V V_uni V
  /-Main argument.-/
  intro x x_in_clos
  rcases mem_closure_iff_ball.1 x_in_clos (dynamical_of_uni_is_uni h W_uni n)
    with ⟨y, y_in_ball_x, y_in_F⟩
  specialize s_cover y_in_F
  simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at s_cover
  rcases s_cover with ⟨z, z_in_s, y_in_ball_z⟩
  simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop]
  use z
  apply And.intro z_in_s
  rw [mem_ball_symmetry (dynamical_of_symm_is_symm T W_symm n)] at y_in_ball_x
  apply ball_mono (dynamical_of_comp_is_comp T U W n) z
  exact mem_ball_comp y_in_ball_z y_in_ball_x

theorem cover_mincard_of_closure (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X)
    (n : ℕ) :
    Mincard T (closure F) (compRel U V) n ≤ Mincard T F U n := by
  rcases eq_top_or_lt_top (Mincard T F U n) with (mincard_infi | mincard_fin)
  . rw [mincard_infi]
    exact le_top
  . rcases (finite_mincard_iff T F U n).1 mincard_fin with ⟨s, s_cover, s_mincard⟩
    rw [← s_mincard]
    exact mincard_le_card (dyncover_of_closure h V_uni s_cover)

theorem cover_entropy_of_closure (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    CoverEntropy T (closure F) (compRel U V) ≤ CoverEntropy T F U := by
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_of_closure h F U V_uni n

theorem cover_entropy'_of_closure (F : Set X) (U : Set (X × X)) {V : Set (X × X)}
    (V_uni : V ∈ 𝓤 X) :
    CoverEntropy' T (closure F) (compRel U V) ≤ CoverEntropy' T F U := by
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_of_closure h F U V_uni n

theorem entropy_of_closure (F : Set X) :
    Entropy T (closure F) = Entropy T F := by
  apply le_antisymm _ (EntropyMonotoneSpace.entropy_monotone_space₁ T (@subset_closure X F _))
  apply iSup₂_le
  intro U U_uni
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_comp_U⟩
  apply le_iSup₂_of_le V V_uni
  apply le_trans (cover_entropy_antitone_uni T (closure F) V_comp_U)
    (cover_entropy_of_closure h F V V_uni)

theorem entropy'_of_closure (F : Set X) :
    Entropy' T (closure F) = Entropy' T F := by
  apply le_antisymm _ (EntropyMonotoneSpace.entropy'_monotone_space₁ T (@subset_closure X F _))
  apply iSup₂_le
  intro U U_uni
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_comp_U⟩
  apply le_iSup₂_of_le V V_uni
  exact le_trans (cover_entropy'_antitone_uni T (closure F) V_comp_U)
    (cover_entropy'_of_closure h F V V_uni)

end EntropyClosure

#lint
