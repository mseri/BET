/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Topology.UniformSpace.Pi
import BET.TopologicalEntropy.DynamicalNet

/-!
# Topological entropy of a full shift
Computation of the topological entropy of a full shift. Main results are `shift_entropy_eq_log_card`
and `shift_entropy'_eq_log_card`.

TODO: Check the compatibility with `Mathlib.Topology.MetricSpace.PiNat`. The current file uses the
vocabulary of uniform spaces instead of metric spaces, but there are some non-trivial interactions
between both, and maybe some content in common (cylinders).

TODO: Check/modify the terminology. There are some non-trivial choices (definitions of cylinders),
but they seem to be coherent with e.g. `Mathlib.Topology.MetricSpace.PiNat.cylinder`.

TODO: The discrete topology on a `Fintype` is natural (cf. `FintypeCat.botTopology`...).
Write a corresponding instance of `UniformSpace`, and remove `h` in `shift_entropy_eq_log_card` and
`shift_entropy'_eq_log_card`? In any case, the hypothesis `𝓤 A = Filter.principal idRel` may be
reformulated in a nicer way.

TODO: As always, the passage from `Mincard`/`Maxcard` to `CoverEntropy`/`NetEntropy` is much too
painful for its real mathematical content.
-/

namespace EntropyShift

open Function UniformSpace DynamicalUniformity Fintype

/--One-sided shift.-/
def ShiftOS (A : Type _) := fun (u : ℕ → A) ↦ (fun n : ℕ ↦ u (n+1))

theorem ShiftOS_apply {A : Type _} (u : ℕ → A) :
    ShiftOS A u = (fun n : ℕ ↦ u (n+1)) := rfl

theorem ShiftOS_apply' {A : Type _} (u : ℕ → A) (n : ℕ) :
    ShiftOS A u n = u (n+1) := rfl

theorem ShiftOS_ite (A : Type _) (k : ℕ) :
    (ShiftOS A)^[k] = fun (u : ℕ → A) ↦ (fun n : ℕ ↦ u (n+k)) := by
  induction k
  case zero => simp only [iterate_zero, add_zero]; rfl
  case succ k hk =>
    ext u n
    rw [iterate_succ, (Commute.iterate_self (ShiftOS A) k).comp_eq, comp_apply, hk,
      ShiftOS_apply (fun n : ℕ ↦ u (n+k))]
    simp [add_assoc n 1 k, add_comm 1 k]

theorem ShiftOS_ite_apply {A : Type _} (u : ℕ → A) (k : ℕ) :
    (ShiftOS A)^[k] u = (fun n : ℕ ↦ u (n+k)) := by rw [ShiftOS_ite A k]

theorem ShiftOS_ite_apply' {A : Type _} (u : ℕ → A) (k n : ℕ) :
    (ShiftOS A)^[k] u n = u (n+k) := by rw [ShiftOS_ite_apply u k]

theorem uniformContinuous_ShiftOS {A : Type _} [UniformSpace A] :
    UniformContinuous (ShiftOS A) :=
  uniformContinuous_pi.2 (fun n : ℕ ↦ (Pi.uniformContinuous_proj (fun _ : ℕ ↦ A) (n+1)))

/--Cylinders as entourages.-/
def CylUni (A : Type _) (n : ℕ) := {xy : (ℕ → A) × (ℕ → A) | ∀ k < n, xy.1 k = xy.2 k}

theorem cylinder_mem {A : Type _} (n : ℕ) (x y : ℕ → A) :
    (x, y) ∈ (CylUni A n) ↔ ∀ k < n, x k = y k := by simp [CylUni]

@[simp]
theorem cylinder_time_zero {A : Type _} : CylUni A 0 = Set.univ := by simp [CylUni]

theorem cylinder_antitone_time (A : Type _) : Antitone fun n : ℕ ↦ CylUni A n := by
  intro m n m_le_n
  simp only [CylUni, Set.le_eq_subset, Set.setOf_subset_setOf, Prod.forall]
  exact fun x y h k k_lt_m ↦ h k (lt_of_lt_of_le k_lt_m m_le_n)

theorem cylinder_in_uniformity {A : Type _} [UniformSpace A] {U : Set ((ℕ → A) × (ℕ → A))}
    (h : U ∈ 𝓤 (ℕ → A)) :
    ∃ n : ℕ, CylUni A n ⊆ U := by
  rw [Pi.uniformity, Filter.mem_iInf] at h
  rcases h with ⟨I, I_fin, V, hV, U_inter_V⟩
  rw [U_inter_V]; clear U_inter_V U
  rcases Set.Finite.bddAbove I_fin with ⟨n, hn⟩
  use n+1
  simp only [Set.iInter_coe_set, Set.subset_iInter_iff]
  intro i i_in_I
  specialize hV ⟨i, i_in_I⟩
  rcases hV with ⟨W, W_uni, hW⟩
  apply Set.Subset.trans _ hW; clear hW V
  intro (x, y) h_xy
  rw [cylinder_mem (n+1) x y] at h_xy
  specialize h_xy i (lt_of_le_of_lt ((mem_upperBounds.1 hn) i i_in_I) (lt_add_one n))
  simp only [Set.mem_preimage]
  exact h_xy ▸ refl_mem_uniformity W_uni

theorem cylinder_uniformity_basis {A : Type _} [UniformSpace A] (h : 𝓤 A = Filter.principal idRel)
    (U : Set ((ℕ → A) × (ℕ → A))) :
    U ∈ 𝓤 (ℕ → A) ↔ ∃ n : ℕ, CylUni A n ⊆ U := by
  constructor; exact fun h ↦ cylinder_in_uniformity h
  intro h
  rcases h with ⟨n, cyln_sub_U⟩
  apply Filter.sets_of_superset (𝓤 (ℕ → A)) _ cyln_sub_U; clear cyln_sub_U U
  simp only [Filter.mem_sets, Pi.uniformity, Filter.mem_iInf]
  use Set.Ico 0 n
  constructor; exact Set.finite_Ico 0 n
  use fun i ↦ {(x, y) | x i = y i}
  constructor
  . intro i
    rw [h, Filter.mem_comap]
    use idRel
    constructor
    · exact Filter.mem_principal_self idRel
    · intro (x, y); simp
  . ext xy; simp [CylUni]

theorem cylinder_is_uniformity {A : Type _} [UniformSpace A] (h : 𝓤 A = Filter.principal idRel)
    (n : ℕ) :
    CylUni A n ∈ 𝓤 (ℕ → A) := by
  apply (cylinder_uniformity_basis h (CylUni A n)).2
  use n

theorem shift_of_cylinder (A : Type _) {k n : ℕ} (h : 0 < k) (h' : 0 < n) :
    DynamicalUni (ShiftOS A) (CylUni A k) n = CylUni A (n+k-1) := by
  apply Set.ext_iff.2
  intro (x, y)
  rw [dynamical_uni_mem (ShiftOS A) (CylUni A k) n x y, cylinder_mem (n+k-1) x y]
  constructor
  . intro hyp i i_lt_nk
    rcases (lt_or_le i k) with (i_lt_k | i_ge_k)
    . specialize hyp 0 h'
      exact (cylinder_mem k x y).1 hyp i i_lt_k
    . have : i-k+1 < n := by omega
      specialize hyp (i-k+1) this; clear this
      rw [cylinder_mem k ((ShiftOS A)^[i-k+1] x) ((ShiftOS A)^[i-k+1] y)] at hyp
      specialize hyp (k-1) (Nat.sub_one_lt_of_le h (le_refl k))
      rw [ShiftOS_ite_apply' x (i-k+1) (k-1), ShiftOS_ite_apply' y (i-k+1) (k-1)] at hyp
      have : (k-1) + (i-k+1) = i := by omega
      rw [this] at hyp
      exact hyp
  . intro hyp i i_lt_n
    apply (cylinder_mem k ((ShiftOS A)^[i] x) ((ShiftOS A)^[i] y)).2
    intro j j_lt_k
    rw [ShiftOS_ite_apply' x i j, ShiftOS_ite_apply' y i j]
    apply hyp (j+i) (Nat.le_sub_one_of_lt _)
    rw [← Nat.succ_add j i, add_comm n k]
    exact add_lt_add_of_le_of_lt (Nat.succ_le.2 j_lt_k) i_lt_n

lemma cylinder_injection (A : Type _) [Nonempty A] (n : ℕ) :
    ∀ x : Fin n → A, ∃ y : ℕ → A, ∀ i : Fin n, x i = y i := by
  intro x
  use Function.extend Fin.val x (fun _ ↦ Classical.arbitrary A)
  exact fun i ↦ Eq.symm (Function.Injective.extend_apply Fin.val_injective x
    (fun _ ↦ Classical.arbitrary A) i)

theorem shift_mincard (A : Type _) [Fintype A] (k n : ℕ) :
    DynamicalCover.Mincard (ShiftOS A) Set.univ (CylUni A k) n ≤ (card A)^(n+k-1) := by
  classical
  /-WLOG, A is nonempty.-/
  rcases isEmpty_or_nonempty A with (A_emp | A_nemp)
  . have key : IsEmpty (ℕ → A) := by
      apply isEmpty_fun.2
      split_ands
      . use 0
      . exact A_emp
    exact Set.univ_eq_empty_iff.2 key ▸ DynamicalCover.mincard_of_empty ▸ zero_le _
  /-WLOG, n is positive.-/
  rcases Nat.eq_zero_or_pos n with (rfl | n_pos)
  . rw [zero_add]
    apply le_trans (DynamicalCover.mincard_time_zero_le (ShiftOS A) Set.univ (CylUni A k))
    norm_cast
    exact Nat.one_le_pow (k-1) (card A) card_pos
  /-WLOG, k is positive.-/
  rcases Nat.eq_zero_or_pos k with (rfl | k_pos)
  . apply cylinder_time_zero ▸ le_trans (DynamicalCover.mincard_by_univ_le (ShiftOS A) Set.univ n)
    norm_cast
    exact (Nat.one_le_pow (n-1) (card A) card_pos)
  /-Main case.-/
  choose! f f_cyl_id using cylinder_injection A (n+k-1)
  let s := Set.range f
  have _ := Set.fintypeRange f
  have f_inj : Injective f := by
    intro x y fx_eq_fy
    ext i
    rw [f_cyl_id x i, f_cyl_id y i, fx_eq_fy]
  have key : s.toFinset.card = (card A)^(n+k-1) := by
    rw [Set.toFinset_range, Finset.card_image_of_injective Finset.univ f_inj, Finset.card_univ,
      card_fun, card_fin]
  have := @DynamicalCover.mincard_le_card (ℕ → A) (ShiftOS A) Set.univ (CylUni A k) n s.toFinset
  rw [key, Nat.cast_pow (card A) (n+k-1), Set.coe_toFinset s] at this
  apply this; clear this key
  intro x _
  simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop]
  use f (fun i : Fin (n+k-1) ↦ x i)
  simp only [Set.mem_range, exists_apply_eq_apply, ball, Set.mem_preimage, true_and, s]
  rw [shift_of_cylinder A k_pos n_pos, cylinder_mem (n+k-1) _ x]
  exact fun i i_lt_nk ↦ Eq.symm (f_cyl_id (fun i : Fin (n+k-1) ↦ x i) ⟨i, i_lt_nk⟩)

theorem shift_maxcard (A : Type _) [Fintype A] {k n : ℕ} (k_pos : 0 < k) (n_pos : 0 < n) :
    (card A)^(n+k-1) ≤ DynamicalNet.Maxcard (ShiftOS A) Set.univ (CylUni A k) n := by
  classical
  /-WLOG, A is nonempty.-/
  rcases isEmpty_or_nonempty A with (A_emp | A_nemp)
  . rw [card_eq_zero, ENat.coe_zero]
    apply @le_of_eq_of_le ℕ∞ (0^(n + k - 1)) 0 _ _ (zero_pow _) (zero_le _)
    apply ne_of_gt (Nat.sub_pos_of_lt (lt_of_eq_of_lt _ (Nat.add_lt_add_of_le_of_lt n_pos k_pos)))
    simp
  /-Main case.-/
  choose! f f_cyl_id using cylinder_injection A (n+k-1)
  let s := Set.range f
  have _ := Set.fintypeRange f
  have f_inj : Injective f := by
    intro x y fx_eq_fy
    ext i
    rw [f_cyl_id x i, f_cyl_id y i, fx_eq_fy]
  have key : s.toFinset.card = (card A)^(n+k-1) := by
    rw [Set.toFinset_range, Finset.card_image_of_injective Finset.univ f_inj, Finset.card_univ,
      card_fun, card_fin]
  have := @DynamicalNet.card_le_maxcard (ℕ → A) (ShiftOS A) Set.univ (CylUni A k) n s.toFinset
  rw [key, Nat.cast_pow (card A) (n+k-1), Set.coe_toFinset s] at this
  apply this; clear this key
  constructor; exact Set.subset_univ s
  intro x x_in_s y y_in_s h
  simp only [Set.mem_range, s] at x_in_s y_in_s
  rcases x_in_s with ⟨x', fx'_eq_x⟩
  rcases y_in_s with ⟨y', fy'_eq_y⟩
  rw [← fx'_eq_x, ← fy'_eq_y]
  rw [← fx'_eq_x, ← fy'_eq_y, shift_of_cylinder A k_pos n_pos] at h; clear fx'_eq_x x fy'_eq_y y
  rcases h with ⟨z, z_in_bx, z_in_by⟩
  simp only [ball, Set.mem_preimage] at z_in_bx z_in_by
  rw [cylinder_mem (n+k-1) (f x') z] at z_in_bx
  rw [cylinder_mem (n+k-1) (f y') z] at z_in_by
  apply congr (@Eq.refl _ f)
  ext i
  specialize z_in_bx i.val i.2
  specialize z_in_by i.val i.2
  rw [← f_cyl_id x' i] at z_in_bx
  rw [← f_cyl_id y' i] at z_in_by
  rw [z_in_bx, z_in_by]

open ENNReal ERealDiv

lemma technical_lemma {k : ℕ} (h : 0 < k) (x : ENNReal) :
    Filter.Tendsto (fun n ↦ log (x^(n+k-1)) / (n : ENNReal)) Filter.atTop (nhds (log x)) := by
  /-Eliminating log x.-/
  have : (fun n ↦ log (x ^ (n+k-1)) / (n : ENNReal)) = (fun p : EReal × EReal ↦ p.1 * p.2)
      ∘ (fun n : ℕ ↦ Prod.mk (log x) ((((n+k-1 : ℕ) : ENNReal) : EReal) / (n : ENNReal))) := by
    ext n
    simp only [log_pow, mul_comm, comp_apply, EReal.mul_div]
  rw [this]; clear this
  have one_ne_top : (1 : EReal) ≠ ⊤ := by decide
  have key := ContinuousAt.tendsto <| @ERealMulCont.continuousAt_mul (log x, 1)
    (Or.inr WithBot.one_ne_bot) (Or.inr one_ne_top) (Or.inr one_ne_zero) (Or.inr one_ne_zero)
  simp only [mul_one] at key
  apply Filter.Tendsto.comp key; clear key one_ne_top
  rw [Prod.tendsto_iff]
  constructor; exact tendsto_const_nhds
  simp only
  /-Eliminating the EReal coercion.-/
  have : (fun n : ℕ ↦ (((n+k-1 : ℕ) : ENNReal) : EReal) / (n : ENNReal))
      = ENNReal.toEReal ∘ (fun n : ℕ ↦ ((n+k-1 : ℕ) : ENNReal) / (n : ENNReal)) := by
    ext n
    change (((n+k-1 : ℕ) : ENNReal) * ((n : ENNReal)⁻¹) : EReal)
      = (((n+k-1 : ℕ) : ENNReal) / (n : ENNReal) : EReal)
    rw [← EReal.coe_ennreal_mul ((n+k-1 : ℕ) : ENNReal) ((n : ENNReal)⁻¹)]
    rfl
  rw [this]; clear this
  apply @Filter.Tendsto.comp ℕ ENNReal EReal _ ENNReal.toEReal Filter.atTop (nhds 1) (nhds 1)
  . exact ContinuousAt.tendsto (Continuous.continuousAt continuous_coe_ennreal_ereal)
  /- Is there no squeeze theorem in the library? -/
  have limsup_le_one : Filter.limsup (fun n : ℕ ↦ ((n+k-1 : ℕ) : ENNReal) / (n : ENNReal))
      Filter.atTop ≤ 1 := by
    have : ∀ᶠ n : ℕ in Filter.atTop, ((n+k-1 : ℕ) : ENNReal) / (n : ENNReal)
        ≤ 1 + ((k : ENNReal) / (n : ENNReal)) := by
      simp only [Filter.eventually_atTop]
      use 1
      intro n n_ge_1
      rw [← ENNReal.div_self ((not_iff_not.2 Nat.cast_eq_zero).2 (Nat.pos_iff_ne_zero.1 n_ge_1))
        (natCast_ne_top n), ENNReal.div_add_div_same, ← Nat.cast_add n k]
      apply ENNReal.div_le_div_right _ (n : ENNReal)
      exact Nat.cast_le.2 <| Nat.sub_le (n+k) 1
    apply le_trans (Filter.limsup_le_limsup this); clear this h
    apply le_of_eq
    apply Filter.Tendsto.limsup_eq
    have limit_zero := @ENNReal.Tendsto.const_div ℕ Filter.atTop (fun n : ℕ ↦ (n : ENNReal))
      k ⊤ ENNReal.tendsto_nat_nhds_top (Or.inr <| ENNReal.natCast_ne_top k)
    simp only [div_top] at limit_zero
    have key := Filter.Tendsto.add (@tendsto_const_nhds ENNReal ℕ 1 _ Filter.atTop) limit_zero
    rw [add_zero] at key
    exact key
  have one_le_liminf : 1 ≤ Filter.liminf (fun n : ℕ ↦ ((n+k-1 : ℕ) : ENNReal) / (n : ENNReal))
      Filter.atTop := by
    nth_rewrite 1 [← @Filter.liminf_const ENNReal ℕ _ Filter.atTop _ 1]
    apply Filter.liminf_le_liminf
    . simp only [Filter.eventually_atTop]
      use 1
      intro n n_ge_1
      rw [ENNReal.le_div_iff_mul_le
        (Or.inl <| (not_iff_not.2 Nat.cast_eq_zero).2 (Nat.pos_iff_ne_zero.1 n_ge_1))
        (Or.inl <| natCast_ne_top n), one_mul, Nat.cast_le, Nat.add_sub_assoc h n]
      exact Nat.le_add_right n (k-1)
    . use 0
      simp
    . use ⊤
      simp
  exact tendsto_of_le_liminf_of_limsup_le one_le_liminf limsup_le_one

theorem shift_cover_entropy_le_log_card (A : Type _) [Fintype A] (k : ℕ) :
    DynamicalCover.CoverEntropy (ShiftOS A) Set.univ (CylUni A k) ≤ log (card A) := by
  /-WLOG, A is nonempty.-/
  rcases isEmpty_or_nonempty A with (A_emp | A_nemp)
  . have key : IsEmpty (ℕ → A) := by
      apply isEmpty_fun.2
      split_ands
      . use 0
      . exact A_emp
    exact Set.univ_eq_empty_iff.2 key ▸ DynamicalCover.cover_entropy_of_empty ▸ bot_le
  /-WLOG, k is positive.-/
  rcases (Nat.eq_zero_or_pos k) with (rfl | k_pos)
  . rw [cylinder_time_zero]
    have : Nonempty (ℕ → A) := by
      let a := Classical.arbitrary A
      use fun _ : ℕ ↦ a
    rw [DynamicalCover.cover_entropy_by_univ_of_nonempty (ShiftOS A)
      (Set.nonempty_iff_univ_nonempty.1 this), log_one_le_iff]
    norm_cast
    exact Fintype.card_pos
  /-Main case.-/
  have key :
      ((fun n ↦ log (DynamicalCover.Mincard (ShiftOS A) Set.univ (CylUni A k) n) / (n : ENNReal))
      ≤ᶠ[Filter.atTop] fun n ↦ log ((card A)^(n+k-1)) / (n : ENNReal)) := by
    rw [Filter.EventuallyLE, Filter.eventually_atTop]
    use 0
    intro n _
    apply EReal.div_left_mono _ (log_monotone _)
    norm_cast
    rw [← ENat.toENNReal_coe, ENat.toENNReal_le]
    exact shift_mincard A k n
  apply le_of_le_of_eq <| Misc.EReal_liminf_le_liminf key; clear key
  apply Filter.Tendsto.liminf_eq <| technical_lemma k_pos (card A)

theorem shift_net_entropy_ge_log_card (A : Type _) [Fintype A] {k : ℕ} (h : 0 < k) :
    log (card A) ≤ DynamicalNet.NetEntropy (ShiftOS A) Set.univ (CylUni A k) := by
  have key : (fun n ↦ log ((card A)^(n+k-1)) / (n : ENNReal)) ≤ᶠ[Filter.atTop]
      (fun n ↦ log (DynamicalNet.Maxcard (ShiftOS A) Set.univ (CylUni A k) n) / (n : ENNReal))
      := by
    rw [Filter.EventuallyLE, Filter.eventually_atTop]
    use 1
    intro n n_pos
    apply EReal.div_left_mono
    apply log_monotone
    norm_cast
    rw [← ENat.toENNReal_coe, ENat.toENNReal_le]
    exact shift_maxcard A h n_pos
  apply le_of_eq_of_le _ (Misc.EReal_liminf_le_liminf key); clear key
  exact Eq.symm <| Filter.Tendsto.liminf_eq <| technical_lemma h (card A)

theorem shift_entropy_le_log_card (A : Type _) [Fintype A] [UniformSpace A] :
    DynamicalCover.Entropy (ShiftOS A) Set.univ ≤ log (card A) := by
  apply iSup₂_le
  intro U U_uni
  rcases cylinder_in_uniformity U_uni with ⟨n, cyln_in_U⟩
  apply le_trans <| DynamicalCover.cover_entropy_antitone_uni (ShiftOS A) Set.univ
    <| le_trans (cylinder_antitone_time A (Nat.le_add_right n 1)) cyln_in_U
  exact shift_cover_entropy_le_log_card A (n+1)

theorem shift_entropy_eq_log_card {A : Type _} [Fintype A] [UniformSpace A]
    (h : 𝓤 A = Filter.principal idRel) :
    DynamicalCover.Entropy (ShiftOS A) Set.univ = log (card A) := by
  apply le_antisymm (shift_entropy_le_log_card A)
  rw [← DynamicalNet.net_entropy_eq_cover_entropy (ShiftOS A) Set.univ]
  apply le_trans _ (le_iSup₂ (CylUni A 1) (cylinder_is_uniformity h 1))
  exact shift_net_entropy_ge_log_card A zero_lt_one

theorem shift_entropy'_le_log_card (A : Type _) [Fintype A] [UniformSpace A] :
    DynamicalCover.Entropy' (ShiftOS A) Set.univ ≤ log (card A) := by
  rw [← DynamicalCover.entropy_eq_entropy' (ShiftOS A) (InvariantSubset.univ_is_inv (ShiftOS A))]
  exact shift_entropy_le_log_card A

theorem shift_entropy'_eq_log_card {A : Type _} [Fintype A] [UniformSpace A]
    (h : 𝓤 A = Filter.principal idRel) :
    DynamicalCover.Entropy' (ShiftOS A) Set.univ = log (card A) := by
  rw [← DynamicalCover.entropy_eq_entropy' (ShiftOS A) (InvariantSubset.univ_is_inv (ShiftOS A))]
  exact shift_entropy_eq_log_card h

end EntropyShift

#lint
