/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of a full shift
Computation of the topological entropy of a full shift. Main results are `shift_entropy_eq_log_card`
and `shift_entropy'_eq_log_card`.

The full one-sided shift on a finite discrete alphabet has entropy `log |A|`.
We use mathlib's shift, dynamical covers/nets, and exponential-growth API.
The unprimed global theorem retains BET's liminf convention; its primed version
uses mathlib's default limsup entropy. These two theorems retain the original explicit
uniformity hypothesis; `shift_entropy_eq_log_card_of_discrete` expresses discreteness
using `DiscreteUniformity`.

TODO: Check the compatibility with `Mathlib.Topology.MetricSpace.PiNat`. The current file uses the
vocabulary of uniform spaces instead of metric spaces, but there are some non-trivial interactions
between both, and maybe some content in common (cylinders).

TODO: Check/modify the terminology. There are some non-trivial choices (definitions of cylinders),
but they seem to be coherent with e.g. `Mathlib.Topology.MetricSpace.PiNat.cylinder`.
-/

@[expose] public section

namespace EntropyShift

open Function UniformSpace Fintype Dynamics Filter ExpGrowth
open scoped Uniformity ENNReal

/-- The one-sided shift, specialized from mathlib's full shift. -/
abbrev ShiftOS (A : Type*) : (ℕ → A) → (ℕ → A) :=
  SymbolicDynamics.FullShift.shift 1

lemma ShiftOS_apply {A : Type*} (u : ℕ → A) :
    ShiftOS A u = fun n => u (n + 1) := by
  ext n
  simp [ShiftOS, SymbolicDynamics.FullShift.shift, Nat.add_comm]

lemma ShiftOS_apply' {A : Type*} (u : ℕ → A) (n : ℕ) : ShiftOS A u n = u (n + 1) := by
  rw [ShiftOS_apply]

lemma ShiftOS_ite (A : Type*) (k : ℕ) :
    (ShiftOS A)^[k] = fun u n => u (n + k) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    ext u n
    simp [iterate_succ_apply', hk, Nat.add_comm, Nat.add_left_comm]

lemma ShiftOS_ite_apply {A : Type*} (u : ℕ → A) (k : ℕ) :
    (ShiftOS A)^[k] u = fun n => u (n + k) := by rw [ShiftOS_ite]

lemma ShiftOS_ite_apply' {A : Type*} (u : ℕ → A) (k n : ℕ) :
    (ShiftOS A)^[k] u n = u (n + k) := by rw [ShiftOS_ite]

lemma uniformContinuous_ShiftOS {A : Type*} [UniformSpace A] :
    UniformContinuous (ShiftOS A) := by
  apply uniformContinuous_pi.mpr
  intro n
  simpa only [ShiftOS_apply'] using (Pi.uniformContinuous_proj (fun _ : ℕ => A) (n + 1))

/-- Entourage of configurations agreeing on the first `n` coordinates. -/
def CylUni (A : Type*) (n : ℕ) : SetRel (ℕ → A) (ℕ → A) :=
  {xy | ∀ k < n, xy.1 k = xy.2 k}

lemma cylinder_mem {A : Type*} (n : ℕ) (x y : ℕ → A) :
    (x, y) ∈ CylUni A n ↔ ∀ k < n, x k = y k := Iff.rfl

instance cylinder_isRefl (A : Type*) (n : ℕ) : (CylUni A n).IsRefl :=
  ⟨fun _ _ _ => rfl⟩

instance cylinder_isSymm (A : Type*) (n : ℕ) : (CylUni A n).IsSymm :=
  ⟨fun _ _ h k hk => (h k hk).symm⟩

@[simp] lemma cylinder_time_zero {A : Type*} : CylUni A 0 = Set.univ := by
  ext xy
  simp [CylUni]

lemma cylinder_antitone_time (A : Type*) : Antitone (CylUni A) := by
  intro m n h xy hxy k hk
  exact hxy k (hk.trans_le h)

lemma cylinder_in_uniformity {A : Type*} [UniformSpace A] {U : Set ((ℕ → A) × (ℕ → A))}
    (h : U ∈ 𝓤 (ℕ → A)) : ∃ n : ℕ, CylUni A n ⊆ U := by
  rw [Pi.uniformity, Filter.mem_iInf] at h
  obtain ⟨I, hI, V, hV, rfl⟩ := h
  obtain ⟨n, hn⟩ := hI.bddAbove
  refine ⟨n + 1, ?_⟩
  simp only [Set.iInter_coe_set, Set.subset_iInter_iff]
  intro i hi
  obtain ⟨W, hW, hWV⟩ := hV ⟨i, hi⟩
  apply Set.Subset.trans _ hWV
  intro xy hxy
  have heq := hxy i (lt_of_le_of_lt (hn hi) (Nat.lt_succ_self n))
  change (xy.1 i, xy.2 i) ∈ W
  rw [heq]
  exact refl_mem_uniformity hW

lemma cylinder_uniformity_basis {A : Type*} [UniformSpace A]
    (h : 𝓤 A = Filter.principal SetRel.id) (U : Set ((ℕ → A) × (ℕ → A))) :
    U ∈ 𝓤 (ℕ → A) ↔ ∃ n : ℕ, CylUni A n ⊆ U := by
  constructor
  · exact cylinder_in_uniformity
  rintro ⟨n, hn⟩
  apply Filter.mem_of_superset ?_ hn
  simp only [Pi.uniformity, Filter.mem_iInf]
  refine ⟨Set.Ico 0 n, Set.finite_Ico 0 n, fun i => {xy | xy.1 i = xy.2 i}, ?_, ?_⟩
  · intro i
    rw [h, Filter.mem_comap]
    exact ⟨SetRel.id, Filter.mem_principal_self _, fun _ hxy => hxy⟩
  · ext xy
    simp [CylUni]

lemma cylinder_is_uniformity {A : Type*} [UniformSpace A]
    (h : 𝓤 A = Filter.principal SetRel.id) (n : ℕ) : CylUni A n ∈ 𝓤 (ℕ → A) :=
  (cylinder_uniformity_basis h _).mpr ⟨n, Set.Subset.rfl⟩

lemma shift_of_cylinder (A : Type*) {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    dynEntourage (ShiftOS A) (CylUni A k) n = CylUni A (n + k - 1) := by
  ext ⟨x, y⟩
  rw [mem_dynEntourage, cylinder_mem]
  constructor
  · intro h i hi
    rcases lt_or_ge i k with hik | hik
    · exact h 0 hn i hik
    · have htime : i - k + 1 < n := by omega
      have hindex : k - 1 < k := by omega
      have heq := h (i - k + 1) htime (k - 1) hindex
      simpa only [ShiftOS_ite_apply', show k - 1 + (i - k + 1) = i by omega] using heq
  · intro h i hi j hj
    simpa only [ShiftOS_ite_apply'] using h (j + i) (by omega)

lemma cylinder_injection (A : Type*) [Nonempty A] (n : ℕ) :
    ∀ x : Fin n → A, ∃ y : ℕ → A, ∀ i : Fin n, x i = y i := by
  intro x
  exact ⟨Function.extend Fin.val x (fun _ => Classical.arbitrary A), fun i =>
    (Fin.val_injective.extend_apply x (fun _ => Classical.arbitrary A) i).symm⟩

lemma shift_mincard (A : Type*) [Fintype A] (k n : ℕ) :
    coverMincard (ShiftOS A) Set.univ (CylUni A k) n ≤ (card A : ℕ∞) ^ (n + k - 1) := by
  classical
  rcases isEmpty_or_nonempty A with hA | hA
  · have : IsEmpty (ℕ → A) := inferInstance
    rw [Set.univ_eq_empty_iff.mpr inferInstance, coverMincard_empty]
    exact bot_le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coverMincard_zero _ Set.univ_nonempty]
    exact one_le_pow₀ (by exact_mod_cast (card_pos (α := A)))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [cylinder_time_zero, coverMincard_univ _ Set.univ_nonempty]
    exact one_le_pow₀ (by exact_mod_cast (card_pos (α := A)))
  choose f hf using cylinder_injection A (n + k - 1)
  let s : Finset (ℕ → A) := Finset.univ.image f
  have hcover : IsDynCoverOf (ShiftOS A) Set.univ (CylUni A k) n s := by
    intro x _
    refine ⟨f (fun i => x i), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [shift_of_cylinder A hk hn]
    intro i hi
    exact hf (fun i => x i) ⟨i, hi⟩
  apply hcover.coverMincard_le_card.trans
  have hcard : s.card ≤ (card A) ^ (n + k - 1) := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Finset.card_univ] using
      (Finset.card_image_le (s := Finset.univ) (f := f))
  exact_mod_cast hcard

lemma shift_maxcard (A : Type*) [Fintype A] {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (card A : ℕ∞) ^ (n + k - 1) ≤ netMaxcard (ShiftOS A) Set.univ (CylUni A k) n := by
  classical
  rcases isEmpty_or_nonempty A with hA | hA
  · rw [card_eq_zero, Nat.cast_zero, zero_pow (by omega)]
    exact bot_le
  choose f hf using cylinder_injection A (n + k - 1)
  have hinj : Injective f := by
    intro x y hxy
    ext i
    rw [hf x i, hf y i, hxy]
  let s : Finset (ℕ → A) := Finset.univ.image f
  have hnet : IsDynNetIn (ShiftOS A) Set.univ (CylUni A k) n s := by
    refine ⟨Set.subset_univ _, Set.pairwiseDisjoint_iff.mpr ?_⟩
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z, hzx, hzy⟩ := hxy
    rw [shift_of_cylinder A hk hn] at hzx hzy
    apply congrArg f
    ext i
    exact (hf x' i).trans ((hzx i i.isLt).trans ((hzy i i.isLt).symm.trans (hf y' i).symm))
  have hcard : s.card = (card A) ^ (n + k - 1) := by
    simp only [s, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin]
  simpa only [hcard, Nat.cast_pow] using hnet.card_le_netMaxcard

open ENNReal

/-- The limsup cover-entropy bound; this also implies the liminf bound. -/
lemma shift_cover_entropy'_le_log_card (A : Type*) [Fintype A] (k : ℕ) :
    coverEntropyEntourage (ShiftOS A) Set.univ (CylUni A k) ≤ log (card A) := by
  rcases isEmpty_or_nonempty A with hA | hA
  · have : IsEmpty (ℕ → A) := inferInstance
    rw [Set.univ_eq_empty_iff.mpr inferInstance, coverEntropyEntourage_empty]
    exact bot_le
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [cylinder_time_zero, coverEntropyEntourage_univ _ Set.univ_nonempty]
    exact (ENNReal.log_monotone (by exact_mod_cast (card_pos (α := A)) :
      (1 : ENNReal) ≤ card A)).trans_eq' ENNReal.log_one
  apply le_trans (expGrowthSup_le_of_eventually_le (b := (card A : ENNReal) ^ (k - 1))
    (by simp) (Eventually.of_forall fun n => ?_)) expGrowthSup_pow.le
  calc
    (coverMincard (ShiftOS A) Set.univ (CylUni A k) n : ENNReal) ≤
        (card A : ENNReal) ^ (n + k - 1) := by
      exact_mod_cast shift_mincard A k n
    _ = (card A : ENNReal) ^ (k - 1) * (card A : ENNReal) ^ n := by
      rw [show n + k - 1 = n + (k - 1) by omega, pow_add, mul_comm]

lemma shift_cover_entropy_le_log_card (A : Type*) [Fintype A] (k : ℕ) :
    coverEntropyInfEntourage (ShiftOS A) Set.univ (CylUni A k) ≤ log (card A) :=
  (coverEntropyInfEntourage_le_coverEntropyEntourage _ _ _).trans
    (shift_cover_entropy'_le_log_card A k)

lemma shift_net_entropy_ge_log_card (A : Type*) [Fintype A] {k : ℕ} (hk : 0 < k) :
    log (card A) ≤ netEntropyInfEntourage (ShiftOS A) Set.univ (CylUni A k) := by
  rcases isEmpty_or_nonempty A with hA | hA
  · simp [card_eq_zero]
  rw [← expGrowthInf_pow (b := (card A : ENNReal))]
  apply expGrowthInf_eventually_monotone
  filter_upwards [eventually_ge_atTop 1] with n hn
  calc
    (card A : ENNReal) ^ n ≤ (card A : ENNReal) ^ (n + k - 1) :=
      pow_le_pow_right₀ (by exact_mod_cast (card_pos (α := A))) (by omega)
    _ ≤ (netMaxcard (ShiftOS A) Set.univ (CylUni A k) n : ENNReal) := by
      exact_mod_cast shift_maxcard A hk (by omega : 0 < n)

lemma shift_entropy'_le_log_card (A : Type*) [Fintype A] [UniformSpace A] :
    coverEntropy (ShiftOS A) Set.univ ≤ log (card A) := by
  apply iSup₂_le
  intro U hU
  obtain ⟨n, hn⟩ := cylinder_in_uniformity hU
  exact (coverEntropyEntourage_antitone _ _ hn).trans (shift_cover_entropy'_le_log_card A n)

lemma shift_entropy_le_log_card (A : Type*) [Fintype A] [UniformSpace A] :
    coverEntropyInf (ShiftOS A) Set.univ ≤ log (card A) :=
  (coverEntropyInf_le_coverEntropy _ _).trans (shift_entropy'_le_log_card A)

lemma shift_entropy_eq_log_card {A : Type*} [Fintype A] [UniformSpace A]
    (h : 𝓤 A = Filter.principal SetRel.id) :
    coverEntropyInf (ShiftOS A) Set.univ = log (card A) := by
  apply le_antisymm (shift_entropy_le_log_card A)
  exact (shift_net_entropy_ge_log_card A (by decide : 0 < 1)).trans
    (netEntropyInfEntourage_le_coverEntropyInf _ _ (cylinder_is_uniformity h 1))

lemma shift_entropy'_eq_log_card {A : Type*} [Fintype A] [UniformSpace A]
    (h : 𝓤 A = Filter.principal SetRel.id) :
    coverEntropy (ShiftOS A) Set.univ = log (card A) := by
  rw [← coverEntropyInf_eq_coverEntropy _ (Set.mapsTo_univ _ _)]
  exact shift_entropy_eq_log_card h

/-- The full shift on a finite discrete uniform alphabet has entropy `log |A|`. -/
lemma shift_entropy_eq_log_card_of_discrete {A : Type*} [Fintype A] [UniformSpace A]
    [DiscreteUniformity A] : coverEntropy (ShiftOS A) Set.univ = log (card A) :=
  shift_entropy'_eq_log_card (DiscreteUniformity.eq_principal_setRelId A)

end EntropyShift
