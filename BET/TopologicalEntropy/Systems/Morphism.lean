/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import BET.TopologicalEntropy.DynamicalNet

/-!
# Topological entropy of the image of a set under a semiconjugacy
The main lemma is `image_entropy`/`image_entropy'`: the entropy of the image of a set by a
semiconjugacy is the entropy of the set for the inverse image filter. This lemma needs very little
hypotheses, and generalizes many important results.

First, a uniformly continuous semiconjugacy descreases the entropy of subsets:
`image_entropy_uniformContinuous_le`, `image_entropy'_uniformContinuous_le`.

Second, the entropy of `Set.univ` for a subsystem is equal to the entropy of the subset, which
justifies the implementation of the entropy of a subset: `subset_restriction_entropy`.

TODO: Investigate the consequences of `image_entropy` for embeddings.

TODO: There are some interesting related results about the entropy of fibered systems.
-/

namespace EntropyImage

open Function UniformSpace ERealDiv ENNReal DynamicalNet

variable {X Y : Type _} {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T)

theorem preimage_of_dynamical_net {F : Set X} {V : Set (Y × Y)} {n : ℕ} {t : Finset Y}
    (h' : IsDynamicalNetOf T (φ '' F) V n t) :
    ∃ s : Finset X, IsDynamicalNetOf S F ((Prod.map φ φ) ⁻¹' V) n s ∧ t.card ≤ s.card := by
  classical
  rcases t.eq_empty_or_nonempty with (rfl | t_nonempty)
  . use ∅
    simp only [Finset.coe_empty, dynnet_by_empty S F ((Prod.map φ φ) ⁻¹' V) n, Finset.card_empty,
      le_refl, and_self]
  have X_nonempty : Nonempty X := Set.Nonempty.to_type
    (Set.Nonempty.of_image (Set.Nonempty.mono h'.1 t_nonempty))
  have key : ∀ y ∈ t, ∃ x ∈ F, φ x = y := by
    intros y y_in_t
    exact h'.1 y_in_t
  choose! f f_section using key
  use Finset.image f t
  unfold IsDynamicalNetOf
  split_ands
  . intro y y_in_ft
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at y_in_ft
    rcases y_in_ft with ⟨x, ⟨x_in_t, y_eq_fx⟩⟩
    rw [← y_eq_fx]
    exact (f_section x x_in_t).1
  . intros x x_pre_t y y_pre_t inter_nonempty
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at x_pre_t y_pre_t
    rcases x_pre_t with ⟨x', ⟨x'_in_t, fx'_eq_x⟩⟩
    rcases y_pre_t with ⟨y', ⟨y'_in_t, fy'_eq_y⟩⟩
    rw [← fx'_eq_x, ← fy'_eq_y] at inter_nonempty
    rw [← fx'_eq_x, ← fy'_eq_y]; clear fx'_eq_x fy'_eq_y x y
    congr
    apply h'.2 x' x'_in_t y' y'_in_t
    rcases inter_nonempty with ⟨z, z_in_inter⟩
    rw [← DynamicalUniformity.preimage_of_dynamical_uni h V n] at z_in_inter
    simp only [ball, Set.mem_inter_iff, Set.mem_preimage, Prod.map_apply] at z_in_inter
    rw [(f_section x' x'_in_t).2, (f_section y' y'_in_t).2] at z_in_inter
    use (φ z)
    exact z_in_inter
  . suffices key : t ⊆ Finset.image (φ ∘ f) t
    . rw [← Finset.image_image] at key
      exact le_trans (Finset.card_mono key) Finset.card_image_le
    intro x x_in_t
    rw [← (f_section x x_in_t).2, ← @Function.comp_apply X Y Y φ f x]
    exact Finset.mem_image_of_mem (φ ∘ f) x_in_t

theorem image_maxcard (F : Set X) (V : Set (Y × Y)) (n : ℕ) :
    Maxcard T (φ '' F) V n ≤ Maxcard S F ((Prod.map φ φ) ⁻¹' V) n := by
  rcases lt_or_eq_of_le (@le_top ℕ∞ _ _ (Maxcard T (φ '' F) V n)) with (maxcard_fin | maxcard_infi)
  . rcases (finite_maxcard_iff T (φ '' F) V n).1 maxcard_fin with ⟨t, ⟨t_net, t_card⟩⟩
    rcases preimage_of_dynamical_net h t_net with ⟨s, ⟨s_net, s_card⟩⟩
    rw [← t_card]
    exact le_trans (WithTop.coe_le_coe.2 s_card) (card_le_maxcard s_net)
  . apply le_of_le_of_eq le_top
    apply Eq.symm
    apply (infinite_maxcard_iff S F ((Prod.map φ φ) ⁻¹' V) n).2
    intro k
    rcases (infinite_maxcard_iff T (φ '' F) V n).1 maxcard_infi k with ⟨t, ⟨t_net, t_card⟩⟩
    rcases preimage_of_dynamical_net h t_net with ⟨s, ⟨s_net, s_card⟩⟩
    use s
    exact ⟨s_net, le_trans t_card s_card⟩

theorem image_net_entropy (F : Set X) (V : Set (Y × Y)) :
    NetEntropy T (φ '' F) V ≤ NetEntropy S F ((Prod.map φ φ) ⁻¹' V) := by
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact image_maxcard h F V n

theorem image_net_entropy' (F : Set X) (V : Set (Y × Y)) :
    NetEntropy' T (φ '' F) V ≤ NetEntropy' S F ((Prod.map φ φ) ⁻¹' V) := by
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact image_maxcard h F V n

end EntropyImage

namespace EntropyImage

open InvariantSubset Function UniformSpace ERealDiv ENNReal DynamicalUniformity DynamicalCover

variable {X Y : Type _} {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T)

theorem image_of_dynamical_cover {F : Set X} {V : Set (Y × Y)} (V_symm : SymmetricRel V) {n : ℕ}
    {t : Finset Y} (h' : IsDynamicalCoverOf T (φ '' F) V n t) :
    ∃ s : Finset X, IsDynamicalCoverOf S F ((Prod.map φ φ) ⁻¹' (compRel V V)) n s
    ∧ s.card ≤ t.card := by
  classical
  rcases isEmpty_or_nonempty X with (X_empty | X_nonempty)
  . use ∅
    rw [Set.eq_empty_of_isEmpty F, Finset.coe_empty, Finset.card_empty]
    simp only [dyncover_of_empty, zero_le, and_self]
  rcases cover_elim h' with ⟨t', ⟨t'_cover, t'_card, t'_nemp_inter⟩⟩
  replace t'_nemp_inter := fun (x : Y) (h : x ∈ t') ↦ Set.nonempty_def.1 (t'_nemp_inter x h)
  choose! g gt'_cover using t'_nemp_inter
  have : ∀ y ∈ φ '' F, ∃ x ∈ F, φ x = y := fun (y : Y) a ↦ a
  choose! f f_section using this
  use Finset.image f (Finset.image g t')
  constructor
  . intro x x_in_F
    specialize t'_cover (Set.mem_image_of_mem φ x_in_F)
    simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop] at t'_cover
    rcases t'_cover with ⟨y, y_in_t', hy⟩
    specialize gt'_cover y y_in_t'
    specialize f_section (g y) gt'_cover.2
    simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, Finset.mem_image,
      exists_exists_and_eq_and, exists_prop]
    use y
    use y_in_t'
    have key := mem_comp_of_mem_ball (dynamical_of_symm_is_symm T V_symm n) gt'_cover.1 hy
    rw [← f_section.2] at key
    rw [← preimage_of_dynamical_uni h (compRel V V) n]
    exact (dynamical_of_comp_is_comp T V V n) key
  . exact le_trans Finset.card_image_le (le_trans Finset.card_image_le t'_card)

theorem image_mincard (F : Set X) {V : Set (Y × Y)} (V_symm : SymmetricRel V) (n : ℕ) :
    Mincard S F ((Prod.map φ φ) ⁻¹' (compRel V V)) n ≤ Mincard T (φ '' F) V n := by
  rcases lt_or_eq_of_le (@le_top ℕ∞ _ _ (Mincard T (φ '' F) V n)) with (mincard_fin | mincard_infi)
  . rcases (finite_mincard_iff T (φ '' F) V n).1 mincard_fin with ⟨t, ⟨t_cover, t_card⟩⟩
    rcases image_of_dynamical_cover h V_symm t_cover with ⟨s, ⟨s_cover, s_card⟩⟩
    rw [← t_card]
    exact le_trans (mincard_le_card s_cover) (WithTop.coe_le_coe.2 s_card)
  . rw [mincard_infi]
    exact le_top

theorem image_cover_entropy (F : Set X) {V : Set (Y × Y)} (V_symm : SymmetricRel V) :
    CoverEntropy S F ((Prod.map φ φ) ⁻¹' (compRel V V)) ≤ CoverEntropy T (φ '' F) V := by
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact image_mincard h F V_symm n

theorem image_cover_entropy' (F : Set X) {V : Set (Y × Y)} (V_symm : SymmetricRel V) :
    CoverEntropy' S F ((Prod.map φ φ) ⁻¹' (compRel V V)) ≤ CoverEntropy' T (φ '' F) V := by
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact image_mincard h F V_symm n

theorem image_entropy {X Y : Type _} (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    Entropy T (φ '' F) = @Entropy X (comap φ u) S F := by
  apply le_antisymm
  . rw [← DynamicalNet.net_entropy_eq_cover_entropy,
      ← @DynamicalNet.net_entropy_eq_cover_entropy X (comap φ u) S F]
    apply iSup₂_le
    intros V V_uni
    apply le_trans (image_net_entropy h F V)
    apply @DynamicalNet.net_entropy_le_entropy X (comap φ u) S F
    rw [uniformity_comap φ, Filter.mem_comap]
    use V
  . apply iSup₂_le
    intros U U_uni
    simp only [uniformity_comap φ, Filter.mem_comap] at U_uni
    rcases U_uni with ⟨V, ⟨V_uni, V_sub⟩⟩
    rcases comp_symm_mem_uniformity_sets V_uni with ⟨W, ⟨W_uni, W_symm, WW_sub_V⟩⟩
    apply le_trans _ (le_iSup₂ W W_uni)
    apply le_trans _ (image_cover_entropy h F W_symm)
    exact (cover_entropy_antitone_uni S F) (le_trans (Set.preimage_mono WW_sub_V) V_sub)

theorem image_entropy' {X Y : Type _} (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    Entropy' T (φ '' F) = @Entropy' X (comap φ u) S F := by
  apply le_antisymm
  . rw [← DynamicalNet.net_entropy'_eq_cover_entropy',
      ← @DynamicalNet.net_entropy'_eq_cover_entropy' X (comap φ u) S F]
    apply iSup₂_le
    intros V V_uni
    apply le_trans (image_net_entropy' h F V)
    apply @DynamicalNet.net_entropy'_le_entropy' X (comap φ u) S F
    rw [uniformity_comap φ, Filter.mem_comap]
    use V
  . apply iSup₂_le
    intros U U_uni
    simp only [uniformity_comap φ, Filter.mem_comap] at U_uni
    rcases U_uni with ⟨V, ⟨V_uni, V_sub⟩⟩
    rcases comp_symm_mem_uniformity_sets V_uni with ⟨W, ⟨W_uni, W_symm, WW_sub_V⟩⟩
    apply le_trans _ (le_iSup₂ W W_uni)
    apply le_trans _ (image_cover_entropy' h F W_symm)
    exact (cover_entropy'_antitone_uni S F) (le_trans (Set.preimage_mono WW_sub_V) V_sub)

theorem image_entropy_uniformContinuous_le {X Y : Type _} [UniformSpace X] [UniformSpace Y]
    {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) (h' : UniformContinuous φ)
    (F : Set X) :
    Entropy T (φ '' F) ≤ Entropy S F := by
  rw [image_entropy _ h F]
  exact entropy_antitone_filter S F (uniformContinuous_iff.1 h')

theorem image_entropy'_uniformContinuous_le {X Y : Type _} [UniformSpace X] [UniformSpace Y]
    {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) (h' : UniformContinuous φ)
    (F : Set X) :
    Entropy' T (φ '' F) ≤ Entropy' S F := by
  rw [image_entropy' _ h F]
  exact entropy'_antitone_filter S F (uniformContinuous_iff.1 h')

/--Restriction of a transformation to an invariant subset.-/
def transform_restrict {X : Type _} {T : X → X} {F : Set X} (h : IsInvariant T F) : F → F :=
  Set.MapsTo.restrict T F F (fun (x : X) (h' : x ∈ F) ↦ inv_def' h h')

theorem subset_restriction_entropy {X : Type _} (u : UniformSpace X) {T : X → X} {F : Set X}
    (h : IsInvariant T F) :
    Entropy (transform_restrict h) Set.univ = Entropy T F := by
  have h' : Semiconj (fun x : F ↦ x.val) (transform_restrict h) T := by
    simp only [Semiconj, Subtype.forall, transform_restrict]
    intros x _
    simp only [Set.MapsTo.val_restrict_apply]
  rw [← image_entropy u h' Set.univ, Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]

/- TODO : Is it possible to have an implicit instance of UniformSpace X instead of an explicit
  argument ?-/


end EntropyImage

/- TODO : Try to get a lower bound on the entropy of the image. What is a right hypothesis on φ ?
  Of course UX ≤ UniformSpace.comap φ UY works, but are there "natural" statements
  (proper map...) ? -/


#lint
