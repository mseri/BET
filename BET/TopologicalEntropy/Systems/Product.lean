/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import BET.TopologicalEntropy.DynamicalNet

/-!
# Topological entropy of unions
The topological entropy of product is the sum of the topological entropies.

TODO: Ease the manipulation of product of uniformities. Maybe complete the file on uniform spaces.

TODO: Finish the proofs. We have the right estimates on `CoverEntropy` and `NetEntropy`, all is
left is to take the supremum on uniformities, using the description of the uniform structure on
a product.

TODO: The manipulation of logarithms and limits is still too painful.

TODO: Extend it to finite products.
-/

namespace DynamicalCoverProduct

open ERealDiv ENNReal DynamicalUniformity Misc
open DynamicalCover DynamicalNet

theorem cover_of_product {X Y : Type _} {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y}
    {U : Set (X × X)} {V : Set (Y × Y)} {n : ℕ} {s : Set X} {t : Set Y}
    (h_S : IsDynamicalCoverOf S F U n s) (h_T : IsDynamicalCoverOf T G V n t) :
  IsDynamicalCoverOf (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n (s ×ˢ t) := by
  unfold IsDynamicalCoverOf
  rw [dynamical_uni_prod S T U V n]
  intro p p_in_FG
  specialize h_S p_in_FG.1
  simp at h_S
  rcases h_S with ⟨x, ⟨x_in_s, p_ball_x⟩⟩
  specialize h_T p_in_FG.2
  simp at h_T
  rcases h_T with ⟨y, ⟨y_in_t, p_ball_y⟩⟩
  rw [Set.mem_iUnion]
  use ⟨(x, y), Set.mem_prod.2 ⟨x_in_s, y_in_t⟩⟩
  simp [ball_prod]
  exact ⟨p_ball_x, p_ball_y⟩

theorem cover_mincard_product {X Y : Type _} (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
  (U : Set (X × X)) (V : Set (Y × Y)) (n : ℕ) :
  Mincard (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n ≤
Mincard S F U n * Mincard T G V n :=
by
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · simp [mincard_of_empty]
  rcases G.eq_empty_or_nonempty with (rfl | G_nonempty)
  · simp [mincard_of_empty]
  rcases eq_top_or_lt_top (Mincard S F U n) with (mincard_X_infi | mincard_X_fin)
  · rw [mincard_X_infi]; clear mincard_X_infi
    apply le_of_le_of_eq le_top _
    apply Eq.symm
    apply WithTop.top_mul
    exact ENat.one_le_iff_ne_zero.1 ((pos_mincard_of_nonempty T G V n).1 G_nonempty)
  rcases eq_top_or_lt_top (Mincard T G V n) with (mincard_Y_infi | mincard_Y_fin)
  · rw [mincard_Y_infi]; clear mincard_Y_infi
    apply le_of_le_of_eq le_top _
    apply Eq.symm
    apply WithTop.mul_top
    exact ENat.one_le_iff_ne_zero.1 ((pos_mincard_of_nonempty S F U n).1 F_nonempty)
  rcases (finite_mincard_iff S F U n).1 mincard_X_fin with ⟨s, ⟨s_cover, s_mincard⟩⟩
  rcases (finite_mincard_iff T G V n).1 mincard_Y_fin with ⟨t, ⟨t_cover, t_mincard⟩⟩
  rw [← s_mincard, ← t_mincard]; clear mincard_X_fin mincard_Y_fin s_mincard t_mincard
  norm_cast
  rw [← Finset.card_product s t]
  apply mincard_le_card
  rw [Finset.coe_product]
  exact cover_of_product s_cover t_cover

theorem cover_entropy'_product {X Y : Type*} (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) :
    CoverEntropy' (Prod.map S T) (F ×ˢ G) (UniformityProd U V)
    ≤ (CoverEntropy' S F U) + (CoverEntropy' T G V) := by
  rcases Set.eq_empty_or_nonempty F with (F_emp | F_nemp)
  . simp only [F_emp, Set.empty_prod, DynamicalCover.cover_entropy'_of_empty, bot_le]
  rcases Set.eq_empty_or_nonempty G with (G_emp | G_nemp)
  . simp only [G_emp, Set.prod_empty, DynamicalCover.cover_entropy'_of_empty, bot_le]
  apply le_trans _ (EReal.limsup_add_le_add_limsup _ _)
  . apply Misc.EReal_limsup_le_limsup <| Filter.eventually_of_forall _
    intro n
    simp
    rw [← EReal.div_right_distrib_of_nneg (nneg_log_mincard_of_nonempty S F_nemp U n)
      (nneg_log_mincard_of_nonempty T G_nemp V n), ← ENNReal.log_mul_add, ← ENat.toENNReal_mul]
    apply EReal.div_left_mono' n _
    apply ENNReal.log_monotone _
    norm_cast
    exact cover_mincard_product S T F G U V n
  . exact Or.inl <| ne_of_gt <| lt_of_lt_of_le EReal.bot_lt_zero
      (DynamicalCover.nneg_cover_entropy'_of_nonempty S F_nemp U)
  . exact Or.inr <| ne_of_gt <| lt_of_lt_of_le EReal.bot_lt_zero
      (DynamicalCover.nneg_cover_entropy'_of_nonempty T G_nemp V)

end DynamicalCoverProduct


namespace NetEntropyProduct

open ERealDiv ENNReal UniformSpace DynamicalUniformity Misc
open DynamicalNet

theorem net_of_product {X Y : Type _} {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y}
{U : Set (X × X)} {V : Set (Y × Y)} {n : ℕ} {s : Set X} {t : Set Y}
(h_S : IsDynamicalNetOf S F U n s) (h_T : IsDynamicalNetOf T G V n t) :
  IsDynamicalNetOf (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n (s ×ˢ t) :=
by
  constructor; exact Set.prod_mono h_S.1 h_T.1
  intros xy_1 xy_1_in_st xy_2 xy_2_in_st h
  rw [dynamical_uni_prod S T U V n] at h
  rcases h with ⟨zw, zw_in_inter⟩
  simp [ball, UniformityProd] at zw_in_inter
  apply Prod.eq_iff_fst_eq_snd_eq.2
  constructor
  . apply h_S.2 xy_1.1 (Set.mem_prod.1 xy_1_in_st).1 xy_2.1 (Set.mem_prod.1 xy_2_in_st).1
    use zw.1
    simp [ball]
    exact ⟨zw_in_inter.1.1, zw_in_inter.2.1⟩
  . apply h_T.2 xy_1.2 (Set.mem_prod.1 xy_1_in_st).2 xy_2.2 (Set.mem_prod.1 xy_2_in_st).2
    use zw.2
    simp [ball]
    exact ⟨zw_in_inter.1.2, zw_in_inter.2.2⟩

theorem net_maxcard_product {X Y : Type _} (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
  (U : Set (X × X)) (V : Set (Y × Y)) (n : ℕ) :
Maxcard S F U n * Maxcard T G V n
  ≤ Maxcard (Prod.map S T) (F ×ˢ G) (UniformityProd U V) n :=
by
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · simp [maxcard_of_empty]
  rcases G.eq_empty_or_nonempty with (rfl | G_nonempty)
  · simp [maxcard_of_empty]
  rcases eq_top_or_lt_top (Maxcard S F U n) with (maxcard_F_infi | maxcard_F_fin)
  · apply le_of_le_of_eq le_top
    apply Eq.symm
    rw [infinite_maxcard_iff]
    intro k
    rw [maxcard_eq_sSup, sSup_eq_top] at maxcard_F_infi
    specialize maxcard_F_infi (k : ℕ∞) (WithTop.coe_lt_top k)
    simp at maxcard_F_infi
    rcases maxcard_F_infi with ⟨s, ⟨s_net, s_card⟩⟩
    rcases G_nonempty with ⟨y, y_in_G⟩
    use s ×ˢ ({y} : Finset Y)
    rw [Finset.coe_product]
    constructor
    . apply net_of_product s_net
      simp
      exact dynnet_by_singleton T V n y_in_G
    . rw [Finset.card_product s ({y} : Finset Y), Finset.card_singleton y, mul_one]
      exact le_of_lt s_card
  rcases eq_top_or_lt_top (Maxcard T G V n) with (maxcard_G_infi | maxcard_G_fin)
  · apply le_of_le_of_eq le_top
    apply Eq.symm
    rw [infinite_maxcard_iff]
    intro k
    rw [maxcard_eq_sSup, sSup_eq_top] at maxcard_G_infi
    specialize maxcard_G_infi (k : ℕ∞) (WithTop.coe_lt_top k)
    simp at maxcard_G_infi
    rcases maxcard_G_infi with ⟨s, ⟨s_net, s_card⟩⟩
    rcases F_nonempty with ⟨x, x_in_G⟩
    use ({x} : Finset X) ×ˢ s
    rw [Finset.coe_product]
    constructor
    . apply net_of_product _ s_net
      simp
      exact dynnet_by_singleton S U n x_in_G
    . rw [Finset.card_product ({x} : Finset X) s, Finset.card_singleton x, one_mul]
      exact le_of_lt s_card
  rcases (finite_maxcard_iff S F U n).1 maxcard_F_fin with ⟨s, ⟨s_cover, s_maxcard⟩⟩
  rcases (finite_maxcard_iff T G V n).1 maxcard_G_fin with ⟨t, ⟨t_cover, t_maxcard⟩⟩
  rw [← s_maxcard, ← t_maxcard]; clear maxcard_F_fin maxcard_G_fin s_maxcard t_maxcard
  norm_cast
  rw [← Finset.card_product s t]
  apply card_le_maxcard
  rw [Finset.coe_product]
  exact net_of_product s_cover t_cover


theorem net_entropy_product {X Y : Type*} (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
  (U : Set (X × X)) (V : Set (Y × Y)) :
(NetEntropy S F U) + (NetEntropy T G V)
  ≤ NetEntropy (Prod.map S T) (F ×ˢ G) (UniformityProd U V) :=
by
  rcases Set.eq_empty_or_nonempty F with (F_emp | F_nemp)
  . simp only [F_emp, DynamicalNet.net_entropy_of_empty, EReal.bot_add, bot_le]
  rcases Set.eq_empty_or_nonempty G with (G_emp | G_nemp)
  . simp only [G_emp, DynamicalNet.net_entropy_of_empty, EReal.add_bot, bot_le]
  apply le_trans (EReal.add_liminf_le_liminf_add _ _)
  . apply Misc.EReal_liminf_le_liminf <| Filter.eventually_of_forall _
    intro n
    simp only [Pi.add_apply]
    rw [← EReal.div_right_distrib_of_nneg (nneg_log_maxcard_of_nonempty S F_nemp U n)
      (nneg_log_maxcard_of_nonempty T G_nemp V n), ← ENNReal.log_mul_add, ← ENat.toENNReal_mul]
    apply EReal.div_left_mono' n _
    apply ENNReal.log_monotone _
    norm_cast
    exact net_maxcard_product S T F G U V n
  . exact Or.inl <| ne_of_gt <| lt_of_lt_of_le EReal.bot_lt_zero
      (DynamicalNet.nneg_net_entropy_of_nonempty S F_nemp U)
  . exact Or.inr <| ne_of_gt <| lt_of_lt_of_le EReal.bot_lt_zero
      (DynamicalNet.nneg_net_entropy_of_nonempty T G_nemp V)


end NetEntropyProduct

#lint
