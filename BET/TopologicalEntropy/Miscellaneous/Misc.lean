import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Topology.UniformSpace.Basic

/-!
# Miscellaneous lemmas
To be inserted in various libraries in Mathlib.

The largest part are various lemmas about limsup/liminf in the extended reals. They
may benefit from some extensions (e.g. `limsup u + liminf v ≤ limsup (u+v)`...) and then
having their own file.

I've also added the specialization to EReal of some existing lemmas (see e.g. `limsup_le_limsup`).
Their current implementation adds some hypotheses which are automatically satistfied for
EReal (`autoparam`...) but still make proofs more cumbersome than they should be.
-/

/-WARNING: The suggestions are the raw outputs of #find_home. They still need to be vetted.-/

namespace Misc

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14019 -/
theorem ENat.top_pow {n : ℕ} (n_pos : 0 < n) : (⊤ : ℕ∞)^n = ⊤ := by
  apply @Nat.le_induction 1 (fun m : ℕ ↦ fun _ : 1 ≤ m ↦ (⊤ : ℕ∞) ^ m = ⊤) (pow_one ⊤)
  · intro m _ h
    calc
      (⊤ : ℕ∞)^(m + 1) = ⊤^m * ⊤^1 := by rw [pow_add ⊤ m 1]
                     _ = ⊤ * ⊤^1   := by rw [h]
                     _ = ⊤ * ⊤     := by rw [pow_one ⊤]
                     _ = ⊤         := WithTop.top_mul_top
  · exact n_pos


/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14066 -/
/-Suggested: Mathlib.Topology.UniformSpace.Basic-/
theorem uniformContinuous_ite {X : Type _} [UniformSpace X] (T : X → X) (n : ℕ)
    (h : UniformContinuous T) :
    UniformContinuous T^[n] := by
  induction' n with n hn
  · exact uniformContinuous_id
  · exact Function.iterate_succ _ _ ▸ UniformContinuous.comp hn h

/- MATHLIB PR: ______ -/
/-Suggested: Mathlib.Order.Monotone.Basic, Mathlib.Algebra.Group.Hom.Defs-/
theorem prod_map_ite {X Y : Type _} (S : X → X) (T : Y → Y) (n : ℕ) :
    (Prod.map S T)^[n] = Prod.map S^[n] T^[n] := by
  induction' n with n hn
  · rw [Function.iterate_zero, Function.iterate_zero, Function.iterate_zero, Prod.map_id]
  · rw [Function.iterate_succ, hn, Prod.map_comp_map, ← Function.iterate_succ,
      ← Function.iterate_succ]

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14096 -/
/-Suggested: Mathlib.Data.Prod.Basic-/
theorem prod_map_comp_swap {X : Type _} (f g : X → X) :
    Prod.map f g ∘ Prod.swap = Prod.swap ∘ Prod.map g f := rfl

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14169 -/
/-Suggested: Mathlib.Order.WithBot-/
theorem WithTop.eq_top_iff_forall {α : Type _} [Preorder α] {x : WithTop α} :
    x = ⊤ ↔ ∀ y : α, y < x := by
  constructor
  · exact fun h ↦ h ▸ fun y ↦ WithTop.coe_lt_top y
  · intro h
    by_contra h'
    rcases WithTop.ne_top_iff_exists.1 h' with ⟨y, hy⟩
    specialize h y
    exact ne_of_lt h hy

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14169 -/
/-Suggested: Mathlib.Order.WithBot-/
theorem WithBot.eq_bot_iff_forall {α : Type _} [Preorder α] {x : WithBot α} :
    x = ⊥ ↔ ∀ y : α, x < y := by
  constructor
  · exact fun h ↦ h ▸ fun y ↦ WithBot.bot_lt_coe y
  · intro h
    by_contra h'
    rcases WithBot.ne_bot_iff_exists.1 h' with ⟨y, hy⟩
    specialize h y
    exact ne_of_lt h (Eq.symm hy)

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14102 -/
/-Suggested: Mathlib.Data.Real.EReal-/
theorem EReal.top_add_ne_bot {x : EReal} (h : x ≠ ⊥) : ⊤ + x = ⊤ := by
  induction x using EReal.rec
  · exfalso; exact h (Eq.refl ⊥)
  · exact EReal.top_add_coe _
  · exact EReal.top_add_top

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14102 -/
/-Suggested: Mathlib.Data.Real.EReal-/
theorem EReal.ne_bot_add_top {x : EReal} (h : x ≠ ⊥) : x + ⊤ = ⊤ := by
  rw [add_comm, EReal.top_add_ne_bot h]

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14102 -/
/-Suggested: Mathlib.Data.Real.EReal-/
theorem EReal.add_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  induction' a using EReal.rec with a
  · exfalso; exact not_lt_bot ha
  · induction' b using EReal.rec with b
    · exfalso; exact not_lt_bot hb
    · norm_cast at *; exact Left.add_pos ha hb
    · exact EReal.ne_bot_add_top (Ne.symm (ne_of_lt (lt_trans EReal.bot_lt_zero ha))) ▸ hb
  · rw [EReal.top_add_ne_bot (Ne.symm (ne_of_lt (lt_trans EReal.bot_lt_zero hb)))]
    exact ha

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14102 -/
/-Suggested: Mathlib.Data.Real.EReal-/
theorem EReal.mul_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  induction' a using EReal.rec with a
  · exfalso; exact not_lt_bot ha
  · induction' b using EReal.rec with b
    · exfalso; exact not_lt_bot hb
    · norm_cast at *; exact Left.mul_pos ha hb
    · rw [mul_comm, EReal.top_mul_of_pos ha]; exact hb
  · rw [EReal.top_mul_of_pos hb]; exact ha

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14125 -/
/-Suggested: Mathlib.Data.Real.EReal-/
@[simp]
theorem EReal.add_sub_cancel_right {a : EReal} {b : Real} : a + b - b = a := by
  induction' a using EReal.rec with a
  · rw [EReal.bot_add b, EReal.bot_sub b]
  · norm_cast; linarith
  · rw [EReal.top_add_ne_bot (EReal.coe_ne_bot b), EReal.top_sub_coe]

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14125 -/
/-Suggested: Mathlib.Data.Real.EReal-/
theorem EReal.right_distrib_of_nneg {a b c : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * c = a * c + b * c := by
  rcases eq_or_lt_of_le ha with (rfl | a_pos)
  · simp
  rcases eq_or_lt_of_le hb with (rfl | b_pos)
  · simp
  clear ha hb
  rcases lt_trichotomy c 0 with (c_neg | rfl | c_pos)
  · induction' c using EReal.rec with c
    · rw [EReal.mul_bot_of_pos a_pos, EReal.mul_bot_of_pos b_pos,
        EReal.mul_bot_of_pos (EReal.add_pos a_pos b_pos), EReal.add_bot ⊥]
    · induction' a using EReal.rec with a
      · exfalso; exact not_lt_bot a_pos
      · induction' b using EReal.rec with b
        · norm_cast
        · norm_cast; exact right_distrib a b c
        · norm_cast
          rw [EReal.ne_bot_add_top (EReal.coe_ne_bot a), EReal.top_mul_of_neg c_neg, EReal.add_bot]
      · rw [EReal.top_add_ne_bot (ne_bot_of_gt b_pos), EReal.top_mul_of_neg c_neg, EReal.bot_add]
    · exfalso; exact not_top_lt c_neg
  · simp
  · induction' c using EReal.rec with c
    · exfalso; exact not_lt_bot c_pos
    · induction' a using EReal.rec with a
      · exfalso; exact not_lt_bot a_pos
      · induction' b using EReal.rec with b
        · norm_cast
        · norm_cast; exact right_distrib a b c
        · norm_cast
          rw [EReal.ne_bot_add_top (EReal.coe_ne_bot a), EReal.top_mul_of_pos c_pos,
            EReal.ne_bot_add_top (EReal.coe_ne_bot (a*c))]
      · rw [EReal.top_add_ne_bot (ne_bot_of_gt b_pos), EReal.top_mul_of_pos c_pos,
          EReal.top_add_ne_bot (ne_bot_of_gt (EReal.mul_pos b_pos c_pos))]
    · rw [EReal.mul_top_of_pos a_pos, EReal.mul_top_of_pos b_pos,
      EReal.mul_top_of_pos (EReal.add_pos a_pos b_pos), EReal.top_add_top]

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14125 -/
/-Suggested: Mathlib.Data.Real.EReal-/
theorem EReal.left_distrib_of_nneg {a b c : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c * (a + b) = c * a + c * b := by
  nth_rewrite 1 [mul_comm]; nth_rewrite 2 [mul_comm]; nth_rewrite 3 [mul_comm]
  exact EReal.right_distrib_of_nneg ha hb

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14125 -/
/-Suggested: Mathlib.Data.Real.EReal-/
theorem EReal.le_iff_le_forall_real_gt (x y : EReal) :
    y ≤ x ↔ ∀ (z : ℝ), (x < z) → (y ≤ z) := by
  constructor
  · exact fun h z x_lt_z ↦ le_trans h (le_of_lt x_lt_z)
  · intro h
    induction' x using EReal.rec with x
    · apply le_of_eq
      apply (EReal.eq_bot_iff_forall_lt y).2
      intro z
      specialize h (z-1) (EReal.bot_lt_coe (z-1))
      apply lt_of_le_of_lt h
      rw [EReal.coe_lt_coe_iff]
      exact sub_one_lt z
    · induction' y using EReal.rec with y
      · exact bot_le
      · norm_cast
        norm_cast at h
        by_contra x_lt_y
        rcases exists_between (lt_of_not_le x_lt_y) with ⟨z, x_lt_z, z_lt_y⟩
        specialize h z x_lt_z
        exact not_le_of_lt z_lt_y h
      · exfalso
        specialize h (x+1) (EReal.coe_lt_coe_iff.2 (lt_add_one x))
        exact not_le_of_lt (EReal.coe_lt_top (x+1)) h
    · exact le_top

open Filter

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
/--The theorem `Filter.liminf_le_liminf` uses two hypotheses (that some sequences are bounded
  under/above). These two hypotheses are always satisfied in EReal.
  This specialization avoids them.-/
theorem EReal_liminf_le_liminf {α : Type _} {f : Filter α} {u v : α → EReal} (h : u ≤ᶠ[f] v) :
    liminf u f ≤ liminf v f := liminf_le_liminf h

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
/--The theorem `Filter.limsup_le_limsup` uses two hypotheses (that some sequences are bounded
  under/above). These two hypotheses are always satisfied in EReal.
  This specialization avoids them.-/
theorem EReal_limsup_le_limsup {α : Type _} {f : Filter α} {u v : α → EReal} (h : u ≤ᶠ[f] v) :
    limsup u f ≤ limsup v f := limsup_le_limsup h

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.limsup_add_le_lt₂ {α : Type _} {f : Filter α} {u v : α → EReal} {a b : EReal}
  (ha : limsup u f < a) (hb : limsup v f < b) :
    limsup (u+v) f ≤ a+b := by
  rcases eq_or_neBot f with (rfl | _); simp only [limsup_bot, bot_le]
  rw [← @limsup_const EReal α _ f _ (a+b)]
  apply EReal_limsup_le_limsup
  apply Eventually.mp (Eventually.and (eventually_lt_of_limsup_lt ha) (eventually_lt_of_limsup_lt hb))
  apply eventually_of_forall
  intros x
  simp only [Pi.add_apply, and_imp]
  exact fun ux_lt_a vx_lt_b ↦ add_le_add (le_of_lt ux_lt_a) (le_of_lt vx_lt_b)

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.limsup_add_bot_ne_top {α : Type _} {f : Filter α} {u : α → EReal} {v : α → EReal}
    (h : limsup u f = ⊥) (h' : limsup v f ≠ ⊤) :
    limsup (u+v) f = ⊥ := by
  apply le_bot_iff.1
  apply (EReal.le_iff_le_forall_real_gt ⊥ (limsup (u+v) f)).2
  intro x
  rcases EReal.exists_between_coe_real (Ne.lt_top h') with ⟨y, ⟨hy, _⟩⟩
  intro trash; clear trash
  rw [← sub_add_cancel x y, EReal.coe_add (x-y) y, EReal.coe_sub x y]
  apply @EReal.limsup_add_le_lt₂ α f u v (x-y) y _ hy
  rw [h, ← EReal.coe_sub x y]
  exact EReal.bot_lt_coe (x-y)

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.limsup_add_le_add_limsup {α : Type _} {f : Filter α} {u v : α → EReal}
    (h : limsup u f ≠ ⊥ ∨ limsup v f ≠ ⊤) (h' : limsup u f ≠ ⊤ ∨ limsup v f ≠ ⊥) :
    limsup (u + v) f ≤ (limsup u f) + (limsup v f) := by
  /- WLOG, ⊥ < limsup u f. -/
  rcases eq_bot_or_bot_lt (limsup u f) with (u_bot | u_nbot)
  · rcases h with (u_nbot | v_ntop)
    · exfalso; exact u_nbot u_bot
    · rw [EReal.limsup_add_bot_ne_top u_bot v_ntop]; exact bot_le
  /- WLOG, ⊥ < limsup v f. -/
  rcases eq_bot_or_bot_lt (limsup v f) with (v_bot | v_nbot)
  · rcases h' with (u_ntop | v_nbot)
    · rw [add_comm, EReal.limsup_add_bot_ne_top v_bot u_ntop]; exact bot_le
    · exfalso; exact v_nbot v_bot
  clear h h'
  /- WLOG, limsup v f < ⊤. -/
  rcases eq_top_or_lt_top (limsup v f) with (v_top | v_ntop)
  · rw [v_top, EReal.ne_bot_add_top (ne_of_gt u_nbot)]; exact le_top
  /- General case. -/
  have limsup_v_real := EReal.coe_toReal (ne_of_lt v_ntop) (ne_of_gt v_nbot)
  apply (EReal.le_iff_le_forall_real_gt _ _).2
  intros x hx
  rcases EReal.lt_iff_exists_real_btwn.1 hx with ⟨y, ⟨sum_lt_y, y_lt_x⟩⟩; clear hx
  have key₁ : limsup u f < (y - limsup v f) := by
    apply lt_of_eq_of_lt _ (EReal.sub_lt_sub_of_lt_of_le sum_lt_y (le_of_eq (Eq.refl (limsup v f)))
      (ne_of_gt v_nbot) (ne_of_lt v_ntop))
    rw [← limsup_v_real, add_sub_cancel_right]
  have key₂ : limsup v f < limsup v f + x - y := by
    rw [← limsup_v_real]
    norm_cast
    norm_cast at y_lt_x
    linarith
  apply le_of_le_of_eq (EReal.limsup_add_le_lt₂ key₁ key₂); clear key₁ key₂ y_lt_x sum_lt_y
  rw [← limsup_v_real]; norm_cast; linarith

/-theorem EReal.limsup_neg {α : Type _} {f : Filter α} {u : α → EReal} :
limsup (-u) f = - liminf u f :=
by
  rw [Filter.limsup_eq_sInf_sSup, Filter.liminf_eq_sSup_sInf, ← EReal.sInf_neg, ← Set.image_comp]
  congr
  apply Set.image_congr'
  intro s
  simp
  rw [ ← EReal.sSup_neg, ← Set.image_comp]
  congr

theorem EReal.liminf_neg {α : Type _} {f : Filter α} {u : α → EReal} :
liminf (-u) f = - limsup u f :=
by
  rw [Filter.liminf_eq_sSup_sInf, Filter.limsup_eq_sInf_sSup, ← EReal.sSup_neg, ← Set.image_comp]
  congr
  apply Set.image_congr'
  intro s
  simp
  rw [ ← EReal.sInf_neg, ← Set.image_comp]
  congr-/

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.ge_iff_le_forall_real_lt (x y : EReal) : y ≤ x ↔ ∀ (z : ℝ), (z < y) → (z ≤ x) := by
  constructor
  · intros h z z_lt_y
    exact le_trans (le_of_lt z_lt_y) h
  · intro h
    induction' x using EReal.rec with x
    · apply le_of_eq
      apply (EReal.eq_bot_iff_forall_lt y).2
      intro z
      apply lt_of_not_le
      intro z_le_y
      apply not_le_of_lt (EReal.bot_lt_coe (z-1))
      specialize h (z-1)
      apply h (lt_of_lt_of_le _ z_le_y)
      norm_cast
      exact sub_one_lt z
    · induction' y using EReal.rec with y
      · exact bot_le
      · norm_cast
        norm_cast at h
        by_contra x_lt_y
        rcases exists_between (lt_of_not_le x_lt_y) with ⟨z, ⟨x_lt_z, z_lt_y⟩⟩
        specialize h z z_lt_y
        exact not_le_of_lt x_lt_z h
      · exfalso
        specialize h (x+1) (EReal.coe_lt_top (x+1))
        norm_cast at h
        exact not_le_of_lt (lt_add_one x) h
    · exact le_top

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
lemma EReal.liminf_add_ge_gt₂ {α : Type _} {f : Filter α} {u v : α → EReal} {a b : EReal}
    (ha : a < liminf u f) (hb : b < liminf v f) :
    a + b ≤ liminf (u + v) f := by
  rcases eq_or_neBot f with (rfl | _); simp only [liminf_bot, le_top]
  rw [← @liminf_const EReal α _ f _ (a+b)]
  apply EReal_liminf_le_liminf
  apply Eventually.mp (Eventually.and
    (eventually_lt_of_lt_liminf ha) (eventually_lt_of_lt_liminf hb))
  apply eventually_of_forall
  intros x
  simp only [Pi.add_apply, and_imp]
  exact fun ux_lt_a vx_lt_b ↦ add_le_add (le_of_lt ux_lt_a) (le_of_lt vx_lt_b)

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
lemma EReal.liminf_add_top_ne_bot {α : Type _} {f : Filter α} {u : α → EReal} {v : α → EReal}
    (h : liminf u f = ⊤) (h' : liminf v f ≠ ⊥) :
    liminf (u + v) f = ⊤ := by
  apply top_le_iff.1
  apply (EReal.ge_iff_le_forall_real_lt (liminf (u+v) f) ⊤).2
  intro x
  rcases EReal.exists_between_coe_real (Ne.bot_lt h') with ⟨y, ⟨_, hy⟩⟩
  intro trash; clear trash
  rw [← sub_add_cancel x y, EReal.coe_add (x-y) y, EReal.coe_sub x y]
  apply @EReal.liminf_add_ge_gt₂ α f u v (x-y) y _ hy
  rw [h, ← EReal.coe_sub x y]
  exact EReal.coe_lt_top (x-y)

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.add_liminf_le_liminf_add {α : Type _} {f : Filter α} {u v : α → EReal}
    (h : liminf u f ≠ ⊥ ∨ liminf v f ≠ ⊤) (h' : liminf u f ≠ ⊤ ∨ liminf v f ≠ ⊥) :
    (liminf u f) + (liminf v f) ≤ liminf (u + v) f:= by
  /- WLOG, liminf v f < ⊤. -/
  rcases eq_top_or_lt_top (liminf v f) with (v_top | v_ntop)
  · rcases h with (u_nbot | v_ntop)
    · rw [add_comm u v, EReal.liminf_add_top_ne_bot v_top u_nbot]; exact le_top
    · exfalso; exact v_ntop v_top
  clear h h'
  /- WLOG, ⊥ < liminf v f. -/
  rcases eq_bot_or_bot_lt (liminf v f) with (v_bot | v_nbot)
  · rw [v_bot, EReal.add_bot]; exact bot_le
  /- General case. -/
  have liminf_v_real := EReal.coe_toReal (ne_of_lt v_ntop) (ne_of_gt v_nbot)
  apply (EReal.ge_iff_le_forall_real_lt _ _).2
  intros x hx
  rcases EReal.lt_iff_exists_real_btwn.1 hx with ⟨y, ⟨x_lt_y, y_lt_sum⟩⟩; clear hx
  have key₁ : (y - liminf v f) < liminf u f := by
    apply lt_of_lt_of_eq (EReal.sub_lt_sub_of_lt_of_le y_lt_sum (le_of_eq (Eq.refl (liminf v f)))
      (ne_of_gt v_nbot) (ne_of_lt v_ntop))
    rw [← liminf_v_real, add_sub_cancel_right]
  have key₂ : liminf v f + x - y < liminf v f := by
    rw [← liminf_v_real]
    norm_cast
    norm_cast at x_lt_y
    linarith
  apply le_of_eq_of_le _ (EReal.liminf_add_ge_gt₂ key₁ key₂); clear key₁ key₂ x_lt_y y_lt_sum
  rw [← liminf_v_real]
  norm_cast
  linarith

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.limsup_le_iff {α : Type _} {f : Filter α} {u : α → EReal} {b : EReal} :
    limsup u f ≤ b ↔ ∀ c : ℝ, b < c → ∀ᶠ a : α in f, u a ≤ c := by
  rw [EReal.le_iff_le_forall_real_gt]
  constructor
  · intro h c b_lt_c
    rcases EReal.exists_between_coe_real b_lt_c with ⟨d, b_lt_d, d_lt_c⟩
    specialize h d b_lt_d
    have key := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt h d_lt_c)
    apply Filter.mem_of_superset key
    simp only [Set.setOf_subset_setOf]
    exact fun a h' ↦ le_of_lt h'
  · intro h c b_lt_c
    rcases eq_or_neBot f with (rfl | _)
    · simp only [limsup_bot, bot_le]
    · specialize h c b_lt_c
      rw [← @Filter.limsup_const EReal α _ f _ (c : EReal)]
      exact limsup_le_limsup h

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.limsup_le_const_forall {α : Type _} {f : Filter α} {u : α → EReal} {b : EReal}
    (h : ∀ a : α, u a ≤ b) :
    limsup u f ≤ b := by
  apply EReal.limsup_le_iff.2
  exact fun c b_lt_c ↦ eventually_of_forall (fun a : α ↦ le_trans (h a) (le_of_lt b_lt_c))

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.const_le_limsup_forall {α : Type _} {f : Filter α} [NeBot f] {u : α → EReal}
    {b : EReal} (h : ∀ a : α, b ≤ u a) :
    b ≤ limsup u f := by
  rw [← @Filter.limsup_const EReal α _ f _ b]
  exact EReal_limsup_le_limsup (eventually_of_forall h)

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.liminf_le_const_forall {α : Type _} {f : Filter α} [NeBot f] {u : α → EReal}
    {b : EReal} (h : ∀ a : α, u a ≤ b) :
    liminf u f ≤ b := by
  rw [← @Filter.liminf_const EReal α _ f _ b]
  exact EReal_liminf_le_liminf (eventually_of_forall h)

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.const_le_liminf_forall {α : Type _} {f : Filter α} {u : α → EReal} {b : EReal}
    (h : ∀ a : α, b ≤ u a) :
    b ≤ liminf u f := by
  rcases eq_or_neBot f with (rfl | _)
  · simp only [liminf_bot, le_top]
  · rw [← @Filter.liminf_const EReal α _ f _ b]
    exact EReal_liminf_le_liminf (eventually_of_forall h)

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/14128 -/
/-Suggested: Mathlib.Topology.Instances.EReal-/
theorem EReal.limsup_max {α : Type _} {f : Filter α} {u v : α → EReal} :
    limsup (fun a ↦ max (u a) (v a)) f = max (limsup u f) (limsup v f) := by
  rcases eq_or_neBot f with (rfl | _); simp [limsup_bot]
  apply le_antisymm
  · apply EReal.limsup_le_iff.2
    intro b hb
    have hu := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_left _ _) hb)
    have hv := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_right _ _) hb); clear hb
    apply Filter.mem_of_superset (Filter.inter_mem hu hv); clear hu hv
    intro a
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, max_le_iff, and_imp]
    exact fun hua hva ↦ ⟨le_of_lt hua, le_of_lt hva⟩
  · apply max_le
    · exact limsup_le_limsup (eventually_of_forall (fun a : α ↦ le_max_left (u a) (v a)))
    · exact limsup_le_limsup (eventually_of_forall (fun a : α ↦ le_max_right (u a) (v a)))

end Misc
