import Mathlib.Tactic
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# Topological dynamics

This file defines Birkhoff sums, other related notions and proves Birkhoff's ergodic theorem.

## Implementation notes

We could do everything in a topological space, using filters and neighborhoods, but it will
be more comfortable with a metric space.

TODO: at some point translate to topological spaces

## References

* ....

-/

open MeasureTheory Filter Metric Function Set
open scoped omegaLimit
set_option autoImplicit false

section Topological_Dynamics

variable {α : Type*} [MetricSpace α]

/-- The non-wandering set of `f` is the set of points which return arbitrarily close after some iterate. -/
def nonWanderingSet (f : α → α) : Set α :=
  {x | ∀ ε, 0 < ε → ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ n ≠ 0}

variable [CompactSpace α] (f : α → α) (hf : Continuous f)

/-- Periodic points belong to the non-wandering set. -/
theorem periodicpts_is_mem (x : α) (n : ℕ) (nnz: n ≠ 0) (pp: IsPeriodicPt f n x) :
    x ∈ nonWanderingSet f := by
  intro ε hε
  use x, n
  refine' ⟨_, _, _⟩
  . exact mem_ball_self hε
  . rw [pp]
    exact mem_ball_self hε
  . exact nnz
  done

lemma periodic_arbitrary_large_time (N : ℕ) (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) (x : α)
    (hx : IsPeriodicPt f m x) :
    ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ N ≤ n := by
  use x, m * N
  refine' ⟨_,_,_⟩
  · exact mem_ball_self hε
  · rw [IsPeriodicPt.mul_const hx N]
    exact mem_ball_self hε
  · exact Nat.le_mul_of_pos_left N hm
  done

lemma inter_subset_empty_of_inter_empty (A : Set α) (B: Set α) (C : Set α) (D: Set α) :
(A ⊆ C) → (B ⊆ D) → (C ∩ D = ∅) → (A ∩ B = ∅) := by
  intro hAC hBD hCD
  have hincl : A ∩ B ⊆ C ∩ D := inter_subset_inter hAC hBD
  rw [hCD] at hincl
  exact Iff.mp subset_empty_iff hincl
  done

lemma separated_balls (x : α) (hfx : x ≠ f x) :  ∃ ε, 0 < ε ∧ (ball x ε) ∩ (f '' (ball x ε)) = ∅ := by
   have hfC : ContinuousAt f x := Continuous.continuousAt hf
   rw [Metric.continuousAt_iff] at hfC
   have h00 : 0 < ((dist x (f x))/4) := by
     apply div_pos
     rw [dist_pos]
     exact hfx
     exact four_pos
   have hfCp := hfC ((dist x (f x))/4) h00
   rcases hfCp with ⟨a, b, c⟩
   use min a ((dist x (f x))/4)
   refine' ⟨_,_⟩
   · exact lt_min b h00
   · rw [Set.ext_iff]
     intro y
     constructor
     · intro ⟨hy1,hy2⟩
       unfold ball at hy1
       dsimp at hy1
       have hha : min a (dist x (f x) / 4) ≤ a := min_le_left a (dist x (f x) / 4)
       have hy3 : dist y x < a := hy1.trans_le hha
       unfold ball at hy2
       rw [mem_image] at hy2
       rcases hy2 with ⟨z , hz1, hz2⟩
       dsimp at hz1
       have hz3 : dist z x < a := hz1.trans_le hha
       have hy4 := c hz3
       rw [hz2] at hy4
       have hha2 : min a (dist x (f x) / 4) ≤ (dist x (f x) / 4) := min_le_right a (dist x (f x) / 4)
       have hy5 : dist y x < (dist x (f x) / 4) := hy1.trans_le hha2
       rw [dist_comm] at hy5
       exfalso
       have gg := dist_triangle x y (f x)
       linarith
     · exact fun l => l.elim
   done

/-- The set of points which are not periodic of any period. -/
def IsNotPeriodicPt (f : α → α)  (x : α) := ∀ n : ℕ, 0 < n -> ¬IsPeriodicPt f n x

lemma separated_ball_image_ball (n : ℕ) (hn : 0 < n) (x : α) (hfx : IsNotPeriodicPt f x) :  ∃ (ε : ℝ), 0 < ε ∧ (ball x ε) ∩ (f^[n] '' (ball x ε)) = ∅ := by
    have hfx2 := hfx n hn
    have hfnC : Continuous f^[n] := Continuous.iterate hf n
    have hfx2' : x ≠ f^[n] x := Ne.symm hfx2
    exact separated_balls (f^[n]) hfnC x hfx2'

lemma separated_balls_along_non_periodic_orbit (N : ℕ) (x : α) (hfx : IsNotPeriodicPt f x) : ∃ δ, (δ > 0) ∧ ∀ (n : ℕ), (0 < n) ∧ (n ≤ N + 1) → (ball x δ) ∩ (f^[n] '' ball x δ) = ∅ := by
  have hkill : ∀ (n : ℕ), 0 < n → ∃ ε, 0 < ε ∧ (ball x ε) ∩ (f^[n] '' (ball x ε)) = ∅ := by
    intro n hnpos
    obtain ⟨ε,hε⟩ := separated_ball_image_ball f hf n hnpos x hfx
    use ε
  choose! ε2 hε2 h'ε2 using hkill
  have A : Finset.Nonempty ((Finset.Icc 1 (N+1)).image ε2) := by simp
  let δ := ((Finset.Icc 1 (N+1)).image ε2).min' A
  have δmem: δ ∈ (Finset.Icc 1 (N+1)).image ε2 := Finset.min'_mem _ _
  simp at δmem
  rcases δmem with ⟨n, ⟨npos, _⟩, h'n⟩
  change ε2 n = δ at h'n
  use δ
  constructor
  exact Eq.trans_gt h'n (hε2 n npos)
  intro  n2 hnrange
  have hA : δ ≤ ε2 n2 := by
    apply Finset.min'_le
    simp
    use n2
    refine' ⟨_, rfl⟩
    apply hnrange
  have hbigball := h'ε2 n2 hnrange.left
  apply inter_subset_empty_of_inter_empty (ball x δ) (f^[n2] '' ball x δ) (ball x (ε2 n2)) (f^[n2] '' ball x (ε2 n2))
  · exact ball_subset_ball (x := x) hA
  · exact image_subset (f^[n2]) (ball_subset_ball (x := x) hA)
  · exact hbigball
  done


theorem ball_non_periodic_arbitrary_large_time (ε : ℝ) (hε : 0 < ε) (x : α) (hx : x ∈ nonWanderingSet f)  (hfx : IsNotPeriodicPt f x) :
 ∀ (N : ℕ), ∃ (n : ℕ), N+1 < n ∧ (f^[n] '' ball x ε) ∩ ball x ε ≠ ∅ := by
  -- Suppose, for sake of contradiction, `∃ N, ∀ (n : ℕ), N + 1 < n → f^[n] '' ball x ε ∩ ball x ε = ∅`
  by_contra h₁
  push_neg at h₁
  -- Since x is not periodic, ∃ ε₂ > 0 such that, ∀ (n : ℕ), 0 < n ∧ n ≤ N + 1 → ball x ε₂ ∩ f^[n] '' ball x ε₂ = ∅.
  obtain ⟨N,h₂⟩ := h₁
  choose ε₂ h₃ using separated_balls_along_non_periodic_orbit f hf N x hfx
  obtain ⟨h₈,h₉⟩ := h₃
  -- Choose ε₃ less than ε and ε₂.
  let ε₃ := min ε ε₂
  have h₅ : ε₃ ≤ ε₂ := min_le_right ε ε₂
  have h₆ : ε₃ ≤ ε := min_le_left ε ε₂
  have hε2 : 0 < ε₃ := by
    rw [lt_min_iff]
    constructor
    exact hε
    exact h₈
  -- We have therefore shown that, for all n, f^n(B(x,ε₃)) ∩ B(x,ε₃) = ∅
  have h₇ : ∀ (n : ℕ), (0 < n) → f^[n] '' ball x ε₃ ∩ ball x ε₃ = ∅ := by
    intro n hnn
    by_cases hcases : n ≤ N + 1
    .apply inter_subset_empty_of_inter_empty (f^[n] '' ball x ε₃) (ball x ε₃)  (f^[n] '' ball x ε₂) (ball x ε₂)
     apply image_subset
     apply ball_subset_ball
     exact h₅
     apply ball_subset_ball
     exact h₅
     rw [inter_comm]
     exact h₉ n ⟨hnn, hcases⟩
    .apply inter_subset_empty_of_inter_empty (f^[n] '' ball x ε₃) (ball x ε₃)  (f^[n] '' ball x ε) (ball x ε)
     apply image_subset
     apply ball_subset_ball
     exact h₆
     apply ball_subset_ball
     exact h₆
     push_neg at hcases
     exact h₂ n hcases
  -- And this contradicts the non wandering assumption.
  unfold nonWanderingSet at hx
  dsimp at hx
  choose y n hy hyn hnpos using hx ε₃ hε2
  push_neg at hnpos
  have hu := h₇ n (Nat.pos_of_ne_zero hnpos)
  have hw := mem_inter (mem_image_of_mem f^[n] hy) hyn
  rw [hu] at hw
  exact hw
  done


lemma non_periodic_arbitrary_large_time (N : ℕ) (ε0 : ℝ) (hε0 : 0 < ε0) (x : α) (hfx : IsNotPeriodicPt f x) (hxf : x ∈ nonWanderingSet f)
: ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε0 ∧ f^[n] y ∈ ball x ε0 ∧ N+1 < n := by
  choose n h2 h3 using (ball_non_periodic_arbitrary_large_time f hf ε0 hε0 x hxf hfx N)
  choose z h5 using (inter_nonempty_iff_exists_left.mp (nmem_singleton_empty.mp h3))
  choose y h7 h8 using ((mem_image f^[n] (ball x ε0) z).mp (mem_of_mem_inter_left h5))
  use! y, n
  have hb : f^[n] y ∈ ball x ε0 := by
    rw [h8]
    exact h5.2
  exact ⟨h7, hb, h2⟩
  done


theorem arbitrary_large_time (N : ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) (hx : x ∈ nonWanderingSet f) :
∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ N + 1 < n :=
by
  by_cases hfx : IsNotPeriodicPt f x
  -- hard case: if x is non-periodic, we use continuity of f
  · exact non_periodic_arbitrary_large_time f hf N ε hε x hfx hx
  -- easy case: if x is periodic, then y = x is a good candidate
  · unfold IsNotPeriodicPt at hfx
    push_neg at hfx
    obtain ⟨n, hn, hn2⟩ := hfx
    -- rcases hfx with ⟨n, hn⟩ also works
    use x
    use n * (N+2)
    refine' ⟨_,_,_⟩
    · exact mem_ball_self hε
    · have h4 : IsPeriodicPt f n x := by
        unfold IsPeriodicPt
        unfold IsFixedPt
        exact hn2
      rw [IsPeriodicPt.mul_const h4 (N+2)]
      exact mem_ball_self hε
    · have h5 := Nat.le_mul_of_pos_left (N + 1) hn
      linarith
  done


/- Show that the non-wandering set of `f` is closed. -/
theorem is_closed : IsClosed (nonWanderingSet f : Set α) := by
  rw [← isSeqClosed_iff_isClosed]
  unfold IsSeqClosed
  intro u x hu ulim
  rw [tendsto_atTop_nhds] at ulim
  intro ε hepos
  have e2pos : 0 < ε / 2 := by linarith
  have h1 : IsOpen (ball x (ε / 2)) := isOpen_ball
  have h2 : ∃ (z : α), z ∈ ball x (ε/ 2) ∧ z ∈ nonWanderingSet f := by
    have k1 := ulim (ball x (ε / 2))
    have k2 : x ∈ (ball x (ε / 2)) := by
      exact mem_ball_self e2pos
    obtain ⟨N, k3⟩ := k1 k2 h1
    have k4 : u N ∈ ball x (ε / 2) := by
      have k5 : N ≤ N := by
        exact Nat.le_refl N
      exact k3 N k5
    exact ⟨u N, k4, hu N⟩
  rcases h2 with ⟨z, h3, h4⟩
  have h5 : ∃ (y : α), ∃ (n : ℕ), y ∈ ball z (ε / 2) ∧ f^[n] y ∈ ball z (ε / 2) ∧ n ≠ 0 := by
    simp [nonWanderingSet] at h4
    -- let l1 := h4 (ε / 2) e2pos
    -- rcases l1 with ⟨y, l1, ⟨n, l2, l3⟩⟩
    -- obtain below is equivalent to the above two lines
    obtain ⟨y, l1, ⟨n, l2, l3⟩⟩ := h4 (ε / 2) e2pos
    use y, n -- note `use y, n` which is the same as `use y` and `use n`
    -- simp -- was repeatedly doing `mem_ball.mp: y ∈ ball x ε -> dist y x < ε `
    exact ⟨l1, l2, l3⟩
  rcases h5 with ⟨y, n, h6, h7, h8⟩
  have h9 : y ∈ ball x ε := by
    -- simp -- was doing `mem_ball.mp: y ∈ ball x ε -> dist y x < ε `
    have m1 : dist y z + dist z x < ε := by
      rw [mem_ball] at h3 h6
      linarith
    have : dist y x ≤ dist y z + dist z x := by
      exact dist_triangle _ _ _  -- why can I omit argument, but I can't in the line below?
    exact lt_of_le_of_lt this m1
  have h10 : f^[n] y ∈ ball x ε := by
    -- simp -- was doing `mem_ball.mp: y ∈ ball x ε -> dist y x < ε `
    have p1 : dist (f^[n] y) z + dist z x < ε := by
      rw [mem_ball] at h7 h3
      linarith
    have : dist (f^[n] y) x ≤ dist (f^[n] y) z + dist z x := by
      exact dist_triangle _ _ _  -- why can I omit argument, but I can't in the line below?
    exact lt_of_le_of_lt this p1
  exact ⟨y, n, h9, h10, h8⟩
  done


/-- The non-wandering set of `f` is compact. -/
theorem is_cpt : IsCompact (nonWanderingSet f : Set α) := by
  apply isCompact_of_isClosed_isBounded
  . exact is_closed f
  . exact isBounded_of_compactSpace
  done

/-- The omega-limit set of any point is nonempty. -/
theorem omegaLimit_nonempty (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) := by
  apply nonempty_omegaLimit atTop (fun n ↦ f^[n]) {x}
  exact Set.singleton_nonempty x
  done

/-- The omega-limit set of any point is contained in the non-wandering set. -/
theorem omegaLimit_nonwandering (x : α) :
    (ω⁺ (fun n ↦ f^[n]) ({x})) ⊆ (nonWanderingSet f) := by
  intro z hz
  rewrite [mem_omegaLimit_iff_frequently] at hz
  simp at hz
  have subsequence : ∀ U ∈ nhds z, ∃ φ, StrictMono φ ∧ ∀ (n : ℕ), f^[φ n] x ∈ U := by
    intro U hU
    apply Filter.extraction_of_frequently_atTop (hz U hU)
    done
  -- unfold nonWanderingSet
  intro ε hε
  have ball_in_nbd : ball z ε ∈ nhds z := by
    exact ball_mem_nhds z hε
  -- same as `let ⟨φ, hφ, hf⟩ := subsequence (ball z ε) ball_in_nbd` but nicer
  obtain ⟨φ, hφ, hf⟩ : ∃ φ, StrictMono φ ∧ ∀ (n : ℕ), f^[φ n] x ∈ ball z ε :=
    subsequence (ball z ε) ball_in_nbd
  use f^[φ 1] x, φ 2 - φ 1
  refine' ⟨_, _, _⟩
  . exact (hf 1)
  . have : f^[φ 2 - φ 1] (f^[φ 1] x) = f^[φ 2] x := by
      rw [ <-Function.iterate_add_apply, Nat.sub_add_cancel ]
      apply le_of_lt;
      apply hφ
      linarith
    rw [this]
    apply (hf 2)
  . simp
    exact Nat.sub_ne_zero_of_lt (hφ Nat.le.refl)
  done

/-- The non-wandering set is non-empty -/
theorem nonWandering_nonempty [hα : Nonempty α] : Set.Nonempty (nonWanderingSet f) := by
  have (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) -> Set.Nonempty (nonWanderingSet f) := by
    apply Set.Nonempty.mono
    apply omegaLimit_nonwandering
  apply this
  apply omegaLimit_nonempty f
  apply Nonempty.some hα
  done


/-- The recurrent set is the set of points that are recurrent, i.e. that belong to their omega-limit set. -/
def recurrentSet {α : Type*} [TopologicalSpace α] (f : α → α) : Set α :=
  { x | x ∈ ω⁺ (fun n ↦ f^[n]) ({x}) }

theorem recurrentSet_iff_accumulation_point (x : α) :
    x ∈ recurrentSet f ↔ ∀ (ε : ℝ) (N : ℕ), 0 < ε
                         -> ∃ m : ℕ, N ≤ m ∧ f^[m] x ∈ ball x ε := by
  constructor
  . intro recur_x
    unfold recurrentSet at recur_x
    -- simp is fine as well, but we only need
    -- `x ∈ { y | p y } = p x` here
    -- I hope that being explicit makes compilation faster
    simp only [mem_setOf_eq] at recur_x
    rw [mem_omegaLimit_iff_frequently] at recur_x
    intro ε N hε
    have recur_x_in_ball := recur_x (ball x ε) (ball_mem_nhds x hε)
    simp [frequently_atTop] at recur_x_in_ball
    exact recur_x_in_ball N
  . intro hf
    unfold recurrentSet
    simp only [mem_setOf_eq] -- `x ∈ { y | p y } = p x`
    rw [mem_omegaLimit_iff_frequently]
    intro U hU
    simp [frequently_atTop] -- reduces the goal to `∀ (a : ℕ), ∃ b, a ≤ b ∧ f^[b] x ∈ U`
    -- same as `rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, rest⟩` but nicer
    obtain ⟨ε, hε, ball_in_U⟩ : ∃ ε, ε > 0 ∧ ball x ε ⊆ U := Metric.mem_nhds_iff.mp hU
    intro a
    obtain ⟨m, hm, fm_in_ball⟩ := (hf ε a hε)
    exact ⟨m, hm, mem_of_subset_of_mem ball_in_U fm_in_ball⟩
  done

/-- Periodic points belong to the recurrent set. -/
theorem periodicpts_mem_recurrentSet
    (x : α) (n : ℕ) (nnz: n ≠ 0) (hx: IsPeriodicPt f n x) :
    x ∈ recurrentSet f := by
  -- unfold IsPeriodicPt at hx
  -- unfold IsFixedPt at hx
  -- unfold recurrentSet
  have x_in_omegaLimit : x ∈ ω⁺ (fun n ↦ f^[n]) ({x} : Set α) := by
    rw [mem_omegaLimit_iff_frequently]
    intro U hU
    simp [frequently_atTop]
    intro a
    have hb : ∃ b, a ≤ b ∧ f^[b] x ∈ U := by
      use a * n
      constructor
      . exact Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero nnz)
      . -- have : f^[a * n] x = x := by
        --  exact Function.IsPeriodicPt.const_mul hx a
        -- rw [this]
        rw [Function.IsPeriodicPt.const_mul hx a]
        exact mem_of_mem_nhds hU
      done
    exact hb
    done
  apply x_in_omegaLimit
  done

/-- The recurrent set is included in the non-wandering set -/
theorem recurrentSet_nonwandering : recurrentSet f ⊆ (nonWanderingSet f) := by
  intro z hz
  unfold recurrentSet at hz
  simp only [mem_setOf_eq] at hz -- `x ∈ { y | p y } = p x`
  apply omegaLimit_nonwandering
  exact hz
  done

/-- The minimal subsets are the closed invariant subsets in which all orbits are dense. -/
structure IsMinimalSubset (f : α → α) (U : Set α) : Prop :=
  (closed : IsClosed U)
  (invariant: IsInvariant (fun n x => f^[n] x) U)
  (minimal: ∀ (x y : α) (_: x ∈ U) (_: y ∈ U) (ε : ℝ), ε > 0 -> ∃ n : ℕ, f^[n] y ∈ ball x ε)

/-- A dynamical system (α,f) is minimal if α is a minimal subset. -/
def IsMinimal (f : α → α) : Prop := IsMinimalSubset f univ

/-- In a minimal dynamics, the recurrent set is all the space. -/
theorem recurrentSet_of_minimal_is_all_space (hf: IsMinimal f) :
    ∀ x : α, x ∈ recurrentSet f := by
  intro z
  have : ∀ (x : α) (ε : ℝ) (N : ℕ), ε > 0
         -> ∃ m : ℕ, m ≥ N ∧ f^[m] x ∈ ball x ε := by
    intro x ε N hε
    obtain ⟨n, hball⟩ : ∃ n, f^[n] (f^[N] x) ∈ ball x ε :=
      hf.minimal x (f^[N] x) (mem_univ _) (mem_univ _) ε hε
    refine' ⟨n + N, _, _⟩
    . linarith
    . rw [ <-Function.iterate_add_apply ] at hball
      exact hball
    done
  apply (recurrentSet_iff_accumulation_point f z).mpr
  exact this z
  done

/-- The doubling map is the classic interval map -/
noncomputable def doubling_map (x : unitInterval) : unitInterval :=
  ⟨Int.fract (2 * x), by exact unitInterval.fract_mem (2 * x)⟩

/-- An example of a continuous dynamics on a compact space in which the recurrent set is all
the space, but the dynamics is not minimal -/
example : ¬IsMinimal (id : unitInterval -> unitInterval) := by
  intro H
  have minimality := H.minimal
  contrapose minimality
  -- `push_neg` pushes negations as deep as possible into the conclusion of a hypothesis
  push_neg
  use 0, 1, (mem_univ 0), (mem_univ 1), (dist (1 : unitInterval) (0 : unitInterval))/2
  -- we need this helper twice below
  have dist_pos : 0 < dist (1 : unitInterval) 0 := by
    apply dist_pos.mpr
    apply unitInterval.coe_ne_zero.mp; norm_num -- 1 ≠ 0
  constructor
  . apply div_pos dist_pos
    linarith -- 0 < 2
  . intro n
    -- `simp` is necessary to go from `¬id^[n] 1 ∈ ball 0 (dist 1 0 / 2)`
    -- to `0 ≤ dist 1 0`
    simp
    exact le_of_lt dist_pos
  done

example (x : unitInterval) :
    x ∈ recurrentSet (id : unitInterval -> unitInterval) := by
  -- unfold recurrentSet
  apply periodicpts_mem_recurrentSet _ _ 1
  . linarith
  . exact is_periodic_id 1 x
  done


/-- Every point in a minimal subset is recurrent. -/
theorem minimalSubset_mem_recurrentSet (U : Set α) (hU: IsMinimalSubset f U) :
      U ⊆ recurrentSet f := by
  intro x hx
  obtain ⟨_, hInv, hMin⟩ := hU
  apply (recurrentSet_iff_accumulation_point f x).mpr
  intro ε N hε
  have iterates_in_U : ∀ n : ℕ, f^[n] x ∈ U := by
    -- unfold IsInvariant at hInv
    intro n
    -- let f' := hInv n; simp at f'
    -- apply Set.mapsTo'.mp at f'
    -- leads us to `f^[n] x ∈ (fun n x ↦ f^[n] x) n '' U`
    -- which simplifies to `∃ x', x' ∈ U ∧ f^[n] x' = f^[n] x`
    -- as one can check with `simp`
    apply Set.mapsTo'.mp (hInv n)
    -- once we `use x`
    -- we get the statement from `exact ⟨hx, rfl⟩`
    -- this can be summarized to
    exact ⟨x, hx, rfl⟩
  obtain ⟨n, hball⟩ : ∃ n, f^[n] (f^[N] x) ∈ ball x ε := by
    apply hMin x (f^[N] x) hx (iterates_in_U N) ε hε
  refine' ⟨n + N, _, _⟩
  . exact le_add_self -- N ≤ n + N
  . rw [ <-Function.iterate_add_apply ] at hball
    exact hball
  done

/-- Every invariant nonempty closed subset contains at least a minimal invariant subset. -/
theorem nonempty_invariant_closed_subset_has_minimalSubset
    (U : Set α) (hne: Nonempty U) (hC: IsClosed U) (hI: IsInvariant (fun n x => f^[n] x) U) :
    ∃ V : Set α, V ⊆ U -> (hinv: MapsTo f U U) -> IsMinimalSubset f U := by
  -- This follows from Zorn's lemma
  sorry



/-- The recurrent set of `f` is nonempty -/
theorem recurrentSet_nonempty [Nonempty α]: Set.Nonempty (recurrentSet f) := by
  sorry

end Topological_Dynamics
