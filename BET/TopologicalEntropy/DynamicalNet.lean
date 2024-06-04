/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import BET.TopologicalEntropy.DynamicalCover

/-!
# Topological entropy via nets
We implement Bowen-Dinaburg's definitions of the topological entropy, via nets.

Many remarks on the topological entropy via covers are still valid.

TODO: Check the vocabulary. I introduced `IsDynamicalCoverOf`, `Maxcard`, `NetEntropy`/
`NetEntropy'` (depending on whether one uses a `liminf` or a `limsup`), `Entropy`/`Entropy'`.
I am not convinced these are the right choices. For instance, I've already encountered `Maxsep`
instead of `Maxcard`. More importantly, having only `Entropy` as the final object
is somewhat too short: it does not differentiate between the cover or net versions,
which makes some statements ambiguous (and requires some care in the opening/closing
of namespaces).

TODO: The most painful part of the manipulation of topological entropy is going from `Maxcard` to
`NetEntropy`/`NetEntropy'`: it involves a logarithm, a division, a `liminf`/`limsup`, and
multiple coercions. It is not helped by the weakness of the libraries on `liminf`/`limsup`.
I have not managed to write sensible proofs. Some clean-up would be welcome, although I think that
the best thing to do would be to write a file on "exponential growth" to make a clean passage
from estimates on `Maxcard` to estimates on `NetEntropy`/`NetEntropy'`.
-/

namespace DynamicalNet

open InvariantSubset DynamicalUniformity UniformSpace

variable {X : Type _}

/-- Given a uniform neighborhood U, an integer n and a subset F, a subset s of F is a (n, U)-net
(i.e. a dynamical net) of F if no two orbits of length n of points in s shadow each other.-/
def IsDynamicalNetOf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
    s ⊆ F ∧ ∀ x ∈ s, ∀ y ∈ s,
    ((ball x (DynamicalUni T U n)) ∩ (ball y (DynamicalUni T U n))).Nonempty → x = y

theorem dynnet_monotone_time {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ} (m_le_n : m ≤ n)
    {s : Set X} (h : IsDynamicalNetOf T F U m s) :
    IsDynamicalNetOf T F U n s := by
  rcases h with ⟨s_sub_F, net_s⟩
  use s_sub_F; clear s_sub_F
  intros x x_in_s y y_in_s h_xy
  apply (net_s x x_in_s y y_in_s); clear net_s
  apply Set.Nonempty.mono _ h_xy; clear h_xy
  exact Set.inter_subset_inter (ball_mono (dynamical_uni_antitone_time T U m_le_n) x)
    (ball_mono (dynamical_uni_antitone_time T U m_le_n) y)

theorem dynnet_antitone_uni {T : X → X} {F : Set X} {U V : Set (X × X)} (U_sub_V : U ⊆ V) {n : ℕ}
    {s : Set X} (h : IsDynamicalNetOf T F V n s) :
    IsDynamicalNetOf T F U n s := by
  rcases h with ⟨s_sub_F, s_net⟩
  use s_sub_F; clear s_sub_F
  intros x x_in_s y y_in_s h_xy
  apply (s_net x x_in_s y y_in_s); clear s_net
  apply Set.Nonempty.mono _ h_xy; clear h_xy
  exact Set.inter_subset_inter (ball_mono (dynamical_uni_monotone_uni T n U_sub_V) x)
    (ball_mono (dynamical_uni_monotone_uni T n U_sub_V) y)

theorem dynnet_by_empty (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    IsDynamicalNetOf T F U n ∅ := by
  constructor
  . exact Set.empty_subset F
  . intros x x_in_empty
    exfalso
    exact Set.not_mem_empty x x_in_empty

theorem dynnet_by_singleton (T : X → X) {F : Set X} (U : Set (X × X)) (n : ℕ) {x : X} (h : x ∈ F) :
    IsDynamicalNetOf T F U n {x} := by
  use Set.singleton_subset_iff.2 h
  simp only [Set.mem_singleton_iff, forall_eq, Set.inter_self, implies_true]

open DynamicalCover

theorem dynnet_le_dyncover {T : X → X} {F : Set X} {U : Set (X × X)} (U_symm : SymmetricRel U)
    {n : ℕ} {s t : Finset X} (hs : IsDynamicalNetOf T F U n s) (ht : IsDynamicalCoverOf T F U n t) :
    s.card ≤ t.card := by
  have : ∀ x ∈ s, ∃ z ∈ t, x ∈ ball z (DynamicalUni T U n) := by
    intro x x_in_s
    specialize ht (hs.1 x_in_s)
    simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop] at ht
    exact ht
  choose! F F_to_cover using this
  apply Finset.card_le_card_of_inj_on F _ _
  . intro x x_in_s
    exact (F_to_cover x x_in_s).1
  . intro x x_in_s y y_in_s Fx_eq_Fy
    apply (hs.2 x x_in_s y y_in_s); clear hs
    use (F x)
    apply Set.mem_inter
    . rw [mem_ball_symmetry (dynamical_of_symm_is_symm T U_symm n)]
      exact (F_to_cover x x_in_s).2
    . rw [Fx_eq_Fy, mem_ball_symmetry (dynamical_of_symm_is_symm T U_symm n)]
      exact (F_to_cover y y_in_s).2

/--The largest cardinal of a (n,U)-dynamical net of F. Takes values in ℕ∞, and is infinite
if and only if F admits nets of arbitrarily large size.-/
noncomputable def Maxcard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨆ (s : Finset X) (_ : IsDynamicalNetOf T F U n s), (s.card : ℕ∞)

theorem maxcard_eq_sSup (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Maxcard T F U n
    = sSup (WithTop.some '' (Finset.card '' {s : Finset X | IsDynamicalNetOf T F U n s})) := by
  unfold Maxcard
  rw [← Set.image_comp, sSup_image]
  simp only [Set.mem_setOf_eq, ENat.some_eq_coe, Function.comp_apply]

theorem finite_maxcard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Maxcard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynamicalNetOf T F U n s ∧ (s.card : ℕ∞) = Maxcard T F U n := by
  constructor
  · intro maxcard_fin
    rcases WithTop.ne_top_iff_exists.1 (ne_of_lt maxcard_fin) with ⟨k, k_maxcard⟩
    rw [← k_maxcard]
    rw [maxcard_eq_sSup T F U n] at k_maxcard
    have h_bdda : BddAbove (Finset.card '' {s : Finset X | IsDynamicalNetOf T F U n s}) := by
      use k
      rw [mem_upperBounds]
      simp only [Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intros s h
      rw [← WithTop.coe_le_coe, k_maxcard]
      apply le_sSup
      simp only [ENat.some_eq_coe, Set.mem_image, Set.mem_setOf_eq, Nat.cast_inj, exists_eq_right]
      use s
    have h_nemp : Set.Nonempty (Finset.card '' {s : Finset X | IsDynamicalNetOf T F U n s}) := by
      use 0
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.card_eq_zero, exists_eq_right,
        Finset.coe_empty]
      exact dynnet_by_empty T F U n
    rw [← WithTop.coe_sSup' h_bdda] at k_maxcard
    norm_cast at k_maxcard
    have key := Nat.sSup_mem h_nemp h_bdda
    rw [← k_maxcard, Set.mem_image] at key
    simp only [Set.mem_setOf_eq] at key
    simp only [ENat.some_eq_coe, Nat.cast_inj]
    exact key
  . intro h
    rcases h with ⟨s, ⟨_, s_maxcard⟩⟩
    rw [← s_maxcard]
    exact WithTop.coe_lt_top s.card

theorem card_le_maxcard {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynamicalNetOf T F U n s) :
    (s.card : ℕ∞) ≤ Maxcard T F U n :=
  @le_iSup₂ ℕ∞ (Finset X) _ _ _ s h

theorem infinite_maxcard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Maxcard T F U n = ⊤ ↔
    ∀ k : ℕ, ∃ s : Finset X, IsDynamicalNetOf T F U n s ∧ k ≤ s.card := by
  constructor
  · intro maxcard_infi k
    rw [maxcard_eq_sSup T F U n, sSup_eq_top] at maxcard_infi
    specialize maxcard_infi (k : ℕ∞) (WithTop.coe_lt_top k)
    simp only [ENat.some_eq_coe, Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and,
      Nat.cast_lt] at maxcard_infi
    rcases maxcard_infi with ⟨s, ⟨s_net, s_card_gt⟩⟩
    use s
    exact ⟨s_net, le_of_lt s_card_gt⟩
  . intro h
    apply Misc.WithTop.eq_top_iff_forall.2
    intro k
    specialize h (k+1)
    rcases h with ⟨s, ⟨s_net, s_card⟩⟩
    apply lt_of_lt_of_le _ (card_le_maxcard s_net)
    rw [ENat.some_eq_coe, Nat.cast_lt]
    exact lt_of_lt_of_le (lt_add_one k) s_card

theorem maxcard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ Maxcard T F U n) := by
  intros m n m_le_n
  simp only
  rw [maxcard_eq_sSup T F U n, maxcard_eq_sSup T F U m]
  apply sSup_le_sSup
  apply Set.image_subset
  apply Set.image_subset
  rw [Set.setOf_subset_setOf]
  intro s
  exact dynnet_monotone_time m_le_n

theorem maxcard_antitone_uni (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X × X) ↦ Maxcard T F U n) := by
  intros U V U_sub_V
  simp only
  rw [maxcard_eq_sSup T F U n, maxcard_eq_sSup T F V n]
  apply sSup_le_sSup
  apply Set.image_subset
  apply Set.image_subset
  rw [Set.setOf_subset_setOf]
  intro s
  exact dynnet_antitone_uni U_sub_V

@[simp]
theorem maxcard_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} : Maxcard T ∅ U n = 0 := by
  unfold Maxcard
  rw [← bot_eq_zero, iSup₂_eq_bot]
  intro s s_net
  replace s_net := Set.subset_empty_iff.1 s_net.1
  norm_cast at s_net
  rw [s_net, Finset.card_empty, CharP.cast_eq_zero, bot_eq_zero']

theorem empty_iff_maxcard_zero (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    F = ∅ ↔ Maxcard T F U n = 0 := by
  constructor
  . intro F_empty
    rw [F_empty, maxcard_of_empty]
  . intro h_maxcard
    rw [Set.eq_empty_iff_forall_not_mem]
    intros x x_in_F
    apply @not_lt_of_le ℕ∞ _ 1 0 _ zero_lt_one
    rw [← h_maxcard]; clear h_maxcard
    apply le_of_eq_of_le _ (le_iSup₂ {x} _)
    . rw [Finset.card_singleton, Nat.cast_one]
    . rw [Finset.coe_singleton]
      exact dynnet_by_singleton T U n x_in_F

theorem pos_maxcard_of_nonempty (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    F.Nonempty ↔ 1 ≤ Maxcard T F U n := by
  rw [ENat.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty]
  apply not_iff_not.2
  exact empty_iff_maxcard_zero T F U n

theorem maxcard_time_zero (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    Maxcard T F U 0 = 1 := by
  apply le_antisymm
  . apply iSup₂_le
    rintro s ⟨_, s_net⟩
    norm_cast
    rw [Finset.card_le_one]
    intros x x_in_s y y_in_s
    apply s_net x x_in_s y y_in_s
    use x
    unfold ball
    rw [dynamical_time_zero, Set.preimage_univ, Set.preimage_univ, Set.inter_self]
    exact Set.mem_univ x
  . exact (pos_maxcard_of_nonempty T F U 0).1 h

theorem net_maxcard_le_cover_mincard (T : X → X) (F : Set X) {U : Set (X × X)} (h : SymmetricRel U)
    (n : ℕ) :
    Maxcard T F U n ≤ Mincard T F U n := by
  rcases (eq_top_or_lt_top (Mincard T F U n)) with (mincard_infi | mincard_fin)
  . rw [mincard_infi]
    exact le_top
  . rcases ((finite_mincard_iff T F U n).1 mincard_fin) with ⟨t, ⟨t_cover, t_mincard⟩⟩
    rw [← t_mincard]
    apply iSup₂_le
    intro s s_net
    norm_cast
    exact dynnet_le_dyncover h s_net t_cover

theorem cover_mincard_comp_le_net_maxcard (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : SymmetricRel U) (n : ℕ) :
    Mincard T F (compRel U U) n ≤ Maxcard T F U n := by
  classical
  rcases (eq_top_or_lt_top (Maxcard T F U n)) with (maxcard_infi | maxcard_fin)
  . rw [maxcard_infi]
    exact le_top
  . rcases ((finite_maxcard_iff T F U n).1 maxcard_fin) with ⟨s, ⟨s_net, s_maxcard⟩⟩
    rw [← s_maxcard]
    apply mincard_le_card
    by_contra h
    unfold DynamicalCover.IsDynamicalCoverOf at h
    rcases Set.not_subset.1 h with ⟨x, ⟨x_in_F, x_not_covered⟩⟩; clear h
    let t := insert x s
    have s_larger_net : IsDynamicalNetOf T F U n t := by
      simp only [IsDynamicalNetOf, Finset.mem_coe]
      constructor
      . simp only [Finset.coe_insert, t]
        intros y y_in_t
        rcases y_in_t with (y_eq_x | y_in_s)
        . rw[y_eq_x]; exact x_in_F
        . exact s_net.1 y_in_s
      . intros y  y_in_t z z_in_t ball_inter
        rcases ball_inter with ⟨w, ⟨w_in_ball_y, w_in_ball_z⟩⟩
        simp only [Finset.mem_insert, t] at y_in_t z_in_t
        rcases y_in_t with (y_eq_x | y_in_s)
        . rw [y_eq_x]; rw [y_eq_x] at w_in_ball_y; clear y_eq_x y
          rcases z_in_t with (z_eq_x | z_in_s)
          . rw [z_eq_x]
          . exfalso
            apply x_not_covered
            simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop]
            use z
            constructor; exact z_in_s
            apply dynamical_of_comp_is_comp T U U n
            rw [mem_ball_symmetry (dynamical_of_symm_is_symm T U_symm n)] at w_in_ball_y
            exact mem_ball_comp w_in_ball_z w_in_ball_y
        . rcases z_in_t with (z_eq_x | z_in_s)
          . rw [z_eq_x]; rw [z_eq_x] at w_in_ball_z; clear z_eq_x z
            exfalso
            apply x_not_covered
            simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop]
            use y
            constructor; exact y_in_s
            apply dynamical_of_comp_is_comp T U U n
            rw [mem_ball_symmetry (dynamical_of_symm_is_symm T U_symm n)] at w_in_ball_z
            exact mem_ball_comp w_in_ball_y w_in_ball_z
          . apply s_net.2 y y_in_s z z_in_s
            use w
            exact ⟨w_in_ball_y, w_in_ball_z⟩
    apply not_le_of_lt _ (card_le_maxcard s_larger_net)
    rw [← s_maxcard]
    simp only [gt_iff_lt, Nat.cast_lt, t]
    apply lt_of_lt_of_eq (lt_add_one s.card)
    apply Eq.symm
    apply Finset.card_insert_of_not_mem
    intro x_in_s
    apply x_not_covered
    simp only [Finset.coe_sort_coe, Set.mem_iUnion, Subtype.exists, exists_prop]
    use x
    constructor
    . exact x_in_s
    . apply @ball_mono X idRel _ _ x
      . simp only [ball, Set.mem_preimage, mem_idRel]
      . apply dynamical_of_rfl_is_rfl T _ n
        exact subset_trans U_rfl (left_subset_compRel U_rfl)

open ENNReal ERealDiv

theorem log_maxcard_of_empty {T : X → X} {U : Set (X × X)} {n : ℕ} : log (Maxcard T ∅ U n) = ⊥ := by
  rw [maxcard_of_empty, ENat.toENNReal_zero, log_zero]

theorem nneg_log_maxcard_of_nonempty (T : X → X) {F : Set X} (F_nonempty : F.Nonempty)
    (U : Set (X × X)) (n : ℕ) :
    0 ≤ log (Maxcard T F U n) := by
  apply log_one_le_iff.1
  rw [← ENat.toENNReal_one, ENat.toENNReal_le]
  exact (pos_maxcard_of_nonempty T F U n).1 F_nonempty

/--The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the
size of the largest (n, U)-dynamical net of F. Takes values in the space fo extended real numbers
[-∞,+∞]. This version uses a limsup.-/
noncomputable def NetEntropy (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.liminf fun n : ℕ ↦ log (Maxcard T F U n) / (n : ENNReal)

/--The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the
size of the largest (n, U)-dynamical net of F. Takes values in the space fo extended real numbers
[-∞,+∞]. This version uses a liminf.-/
noncomputable def NetEntropy' (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.limsup fun n : ℕ ↦ log (Maxcard T F U n) / (n : ENNReal)

theorem net_entropy_antitone_uni (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ NetEntropy T F U) := by
  intros U V U_sub_V
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact maxcard_antitone_uni T F n U_sub_V

theorem net_entropy'_antitone_uni (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ NetEntropy' T F U) := by
  intros U V U_sub_V
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact maxcard_antitone_uni T F n U_sub_V

theorem net_entropy_le' (T : X → X) (F : Set X) (U : Set (X × X)) :
    NetEntropy T F U ≤ NetEntropy' T F U :=
  Filter.liminf_le_limsup

@[simp]
theorem net_entropy'_of_empty {T : X → X} {U : Set (X × X)} : NetEntropy' T ∅ U = ⊥ := by
  suffices h : (fun n : ℕ ↦ (log (Maxcard T ∅ U n)) / (n : ENNReal))
      = (fun _ : ℕ ↦ (⊥ : EReal))
  . unfold NetEntropy'
    rw [h]
    exact Filter.limsup_const ⊥
  . ext1 n
    rw [log_maxcard_of_empty]
    apply EReal.bot_div_ntop
    simp only [ne_eq, natCast_ne_top, not_false_eq_true]

@[simp]
theorem net_entropy_of_empty {T : X → X} {U : Set (X × X)} : NetEntropy T ∅ U = ⊥ :=
  eq_bot_mono (net_entropy_le' T ∅ U) (net_entropy'_of_empty)

theorem nneg_net_entropy_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ NetEntropy T F U := by
  apply le_trans _ Filter.iInf_le_liminf
  apply le_iInf
  exact fun (n : ℕ) ↦ EReal.nneg_div (nneg_log_maxcard_of_nonempty T h U n)

theorem nneg_net_entropy'_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ NetEntropy' T F U :=
  le_trans (nneg_net_entropy_of_nonempty T h U) (net_entropy_le' T F U)

theorem net_entropy_le_cover_entropy (T : X → X) (F : Set X) {U : Set (X × X)}
  (h : SymmetricRel U) :
  NetEntropy T F U ≤ CoverEntropy T F U := by
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact net_maxcard_le_cover_mincard T F h n

theorem cover_entropy_comp_le_net_entropy (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : SymmetricRel U) :
    CoverEntropy T F (compRel U U) ≤ NetEntropy T F U := by
  apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_comp_le_net_maxcard T F U_rfl U_symm n

theorem net_entropy'_le_cover_entropy' (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : SymmetricRel U) :
    NetEntropy' T F U ≤ CoverEntropy' T F U := by
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact net_maxcard_le_cover_mincard T F h n

theorem cover_entropy'_comp_le_net_entropy' (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : SymmetricRel U) :
  CoverEntropy' T F (compRel U U) ≤ NetEntropy' T F U := by
  apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono _
  apply log_monotone _
  rw [ENat.toENNReal_le]
  exact cover_mincard_comp_le_net_maxcard T F U_rfl U_symm n

/-- The entropy of T restricted to F, obtained by taking the supremum over uniformity neighbourhoods.
Note that this supremum is approached by taking small neighbourhoods.-/
noncomputable def Entropy [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ (U : Set (X × X)) (_ : U ∈ 𝓤 X), NetEntropy T F U

/-- An alternative definition of the entropy of T restricted to F, using a liminf instead of
a limsup.-/
noncomputable def Entropy' [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ (U : Set (X × X)) (_ : U ∈ 𝓤 X), NetEntropy' T F U

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

theorem entropy_le_entropy' (T : X → X) (F : Set X) : Entropy T F ≤ Entropy' T F :=
  iSup₂_mono (fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ net_entropy_le' T F U)

theorem net_entropy_le_entropy (T : X → X) (F : Set X) {U : Set (X × X)} (h: U ∈ 𝓤 X) :
    NetEntropy T F U ≤ Entropy T F := by
  apply le_trans _ (le_iSup _ U)
  simp only [h, iSup_pos, le_refl]

theorem net_entropy'_le_entropy' (T : X → X) (F : Set X) {U : Set (X × X)} (h: U ∈ 𝓤 X) :
    NetEntropy' T F U ≤ Entropy' T F := by
  apply le_trans _ (le_iSup _ U)
  simp only [h, iSup_pos, le_refl]

@[simp]
theorem entropy_of_empty {T : X → X} :
Entropy T ∅ = ⊥ := by
  simp only [Entropy, net_entropy_of_empty, iSup_bot]

@[simp]
theorem entropy'_of_empty {T : X → X} :
Entropy' T ∅ = ⊥ := by
  simp only [Entropy', net_entropy'_of_empty, iSup_bot]

theorem nneg_entropy_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) : 0 ≤ Entropy T F := by
  apply le_iSup_of_le Set.univ
  simp only [Filter.univ_mem, iSup_pos]
  exact nneg_net_entropy_of_nonempty T h Set.univ

theorem nneg_entropy'_of_nonempty (T : X → X) {F : Set X} (h : F.Nonempty) : 0 ≤ Entropy' T F :=
  le_trans (nneg_entropy_of_nonempty T h) (entropy_le_entropy' T F)

theorem net_entropy_eq_cover_entropy (T : X → X) (F : Set X) :
    Entropy T F = DynamicalCover.Entropy T F := by
  apply le_antisymm
  . apply iSup₂_le
    intro U U_uni
    apply le_trans (net_entropy_antitone_uni T F (symmetrizeRel_subset_self U)) _
    apply le_trans _ (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_uni))
    exact net_entropy_le_cover_entropy T F (symmetric_symmetrizeRel U)
  . apply iSup₂_le
    intro U U_uni
    rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
    apply le_trans (DynamicalCover.cover_entropy_antitone_uni T F V_comp_U)
      <| le_iSup₂_of_le V V_uni
      <| cover_entropy_comp_le_net_entropy T F (refl_le_uniformity V_uni) V_symm

theorem net_entropy'_eq_cover_entropy' (T : X → X) (F : Set X) :
    Entropy' T F = DynamicalCover.Entropy' T F := by
  apply le_antisymm
  . apply iSup₂_le
    intro U U_uni
    apply le_trans (net_entropy'_antitone_uni T F (symmetrizeRel_subset_self U)) _
    apply le_trans _ (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_uni))
    exact net_entropy'_le_cover_entropy' T F (symmetric_symmetrizeRel U)
  . apply iSup₂_le
    intro U U_uni
    rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
    apply le_trans (DynamicalCover.cover_entropy'_antitone_uni T F V_comp_U)
      <| le_iSup₂_of_le V V_uni
      <| cover_entropy'_comp_le_net_entropy' T F (refl_le_uniformity V_uni) V_symm

theorem net_entropy_eq_cover_entropy' (T : X → X) {F : Set X} (h : IsInvariant T F) :
    Entropy T F = DynamicalCover.Entropy' T F :=
  Eq.trans (net_entropy_eq_cover_entropy T F) (DynamicalCover.entropy_eq_entropy' T h)

theorem net_entropy'_eq_cover_entropy (T : X → X) {F : Set X} (h : IsInvariant T F) :
    Entropy' T F = DynamicalCover.Entropy T F :=
  Eq.trans (net_entropy'_eq_cover_entropy' T F) (Eq.symm (DynamicalCover.entropy_eq_entropy' T h))

theorem net_entropy_eq_net_entropy' (T : X → X) {F : Set X} (h : IsInvariant T F) :
    Entropy T F = Entropy' T F :=
  Eq.trans (net_entropy_eq_cover_entropy' T h) (Eq.symm (net_entropy'_eq_cover_entropy' T F))

end DynamicalNet

#lint
