import CP15.M2K9DistinctGeometry

namespace CP15

private theorem cos_degrees_gt (k c : ℝ)
    (hk0 : 0 ≤ k) (hk90 : k ≤ 90)
    (hcert : c < 1 - 2 *
      (k * (3141593 / 1000000 : ℝ) / 360 -
        (k * (3141592 / 1000000 : ℝ) / 360) ^ 3 / 6 +
        (k * (3141593 / 1000000 : ℝ) / 360) ^ 5 / 100) ^ 2) :
    c < Real.cos (k * Real.pi / 180) := by
  let l : ℝ := k * (3141592 / 1000000 : ℝ) / 360
  let u : ℝ := k * (3141593 / 1000000 : ℝ) / 360
  have hθ0 : 0 ≤ k * Real.pi / 180 := by positivity
  have hθ2 : k * Real.pi / 180 ≤ 2 := by
    nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; positivity
  have hlx : l ≤ (k * Real.pi / 180) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (k * Real.pi / 180) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have h := cos_gt_of_half_interval (k * Real.pi / 180) l u c
    hθ0 hθ2 hl0 hlx hxu hu1 ?_
  · exact h
  · dsimp [l, u]
    exact hcert

private theorem pair_angle_gt_of_box
    (x y : Plane) (g θ c : ℝ)
    (rlo rhi slo shi : ℝ)
    (hrlo0 : 0 < rlo) (hslo0 : 0 < slo)
    (hrlo : rlo ≤ ‖x‖) (hrhi : ‖x‖ ≤ rhi)
    (hslo : slo ≤ ‖y‖) (hshi : ‖y‖ ≤ shi)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hcθ : c < Real.cos θ)
    (hll : pairExpr rlo slo c < 4)
    (hlh : pairExpr rlo shi c < 4)
    (hhl : pairExpr rhi slo c < 4)
    (hhh : pairExpr rhi shi c < 4) :
    θ < g := by
  have hbox := pairExpr_lt_four_of_corners rlo ‖x‖ rhi slo ‖y‖ shi c
    hrlo hrhi hslo hshi hll hlh hhl hhh
  have hpoly : ‖x‖ ^ 2 + ‖y‖ ^ 2 - 4 <
      2 * c * ‖x‖ * ‖y‖ := by
    dsimp [pairExpr] at hbox
    nlinarith
  have hxpos : 0 < ‖x‖ := hrlo0.trans_le hrlo
  have hypos : 0 < ‖y‖ := hslo0.trans_le hslo
  exact polar_pair_angle_gt_of_poly x y g c θ
    hxpos hypos
    hsep hpoly hcos hg0 hgpi hθ0 hθpi hcθ

private theorem cos_deg_52 :
    (615 / 1000 : ℝ) < Real.cos (52 * Real.pi / 180) := by
  apply cos_degrees_gt 52 (615 / 1000) (by norm_num) (by norm_num)
  norm_num

private theorem cos_deg_543 :
    (583 / 1000 : ℝ) < Real.cos ((543 / 10) * Real.pi / 180) := by
  apply cos_degrees_gt (543 / 10) (583 / 1000) (by norm_num) (by norm_num)
  norm_num

private theorem cos_deg_563 :
    (553 / 1000 : ℝ) < Real.cos ((563 / 10) * Real.pi / 180) := by
  apply cos_degrees_gt (563 / 10) (553 / 1000) (by norm_num) (by norm_num)
  norm_num

private theorem cos_deg_783 :
    (201 / 1000 : ℝ) < Real.cos ((783 / 10) * Real.pi / 180) := by
  apply cos_degrees_gt (783 / 10) (201 / 1000) (by norm_num) (by norm_num)
  norm_num

private theorem cos_deg_769 :
    (226 / 1000 : ℝ) < Real.cos ((769 / 10) * Real.pi / 180) := by
  apply cos_degrees_gt (769 / 10) (226 / 1000) (by norm_num) (by norm_num)
  norm_num

private theorem cos_deg_735 :
    (280 / 1000 : ℝ) < Real.cos ((735 / 10) * Real.pi / 180) := by
  apply cos_degrees_gt (735 / 10) (280 / 1000) (by norm_num) (by norm_num)
  norm_num

private theorem ah_box_bound
    (x y : Plane) (g : ℝ) (rlo rhi θ c : ℝ)
    (hrlo0 : 0 < rlo)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hrlo : rlo ≤ ‖x‖) (hrhi : ‖x‖ ≤ rhi)
    (hylo : 2 ≤ ‖y‖) (hyhi : ‖y‖ ≤ 2385436 / 1000000)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi)
    (hcθ : c < Real.cos θ)
    (hll : pairExpr rlo 2 c < 4)
    (hlh : pairExpr rlo (2385436 / 1000000) c < 4)
    (hhl : pairExpr rhi 2 c < 4)
    (hhh : pairExpr rhi (2385436 / 1000000) c < 4) :
    θ < g := by
  exact pair_angle_gt_of_box x y g θ c rlo rhi 2
    (2385436 / 1000000) hrlo0 (by norm_num)
    hrlo hrhi hylo hyhi hsep hcos hg0 hgpi hθ0 hθpi hcθ hll hlh hhl hhh

private theorem al_box_bound
    (x y : Plane) (g : ℝ) (rlo rhi θ c : ℝ)
    (hrlo0 : 0 < rlo)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hrlo : rlo ≤ ‖x‖) (hrhi : ‖x‖ ≤ rhi)
    (hylo : (7 / 5 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ 2)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hgpi : g ≤ Real.pi)
    (hcθ : c < Real.cos θ)
    (hll : pairExpr rlo (7 / 5) c < 4)
    (hlh : pairExpr rlo 2 c < 4)
    (hhl : pairExpr rhi (7 / 5) c < 4)
    (hhh : pairExpr rhi 2 c < 4) :
    θ < g := by
  exact pair_angle_gt_of_box x y g θ c rlo rhi (7 / 5) 2
    hrlo0 (by norm_num) hrlo hrhi hylo hyhi hsep hcos hg0 hgpi
    hθ0 hθpi hcθ hll hlh hhl hhh

/-- The common core radius couples its A-H and A-L angles. Four exact
rectangular corner checks give a strict sum above 127 degrees throughout
the full radial box used in the distinct-blocker branch. -/
theorem distinct_AH_AL_angle_sum_gt_127
    (x h l : Plane) (gH gL : ℝ)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hhlo : (2 : ℝ) ≤ ‖h‖)
    (hhhi : ‖h‖ ≤ 2385436 / 1000000)
    (hllo : (7 / 5 : ℝ) ≤ ‖l‖) (hlhi : ‖l‖ ≤ 2)
    (hsepH : 2 ≤ dist x h) (hsepL : 2 ≤ dist x l)
    (hcosH : Real.cos (polarArg x - polarArg h) = Real.cos gH)
    (hcosL : Real.cos (polarArg x - polarArg l) = Real.cos gL)
    (hH0 : 0 ≤ gH) (hHpi : gH ≤ Real.pi)
    (hL0 : 0 ≤ gL) (hLpi : gL ≤ Real.pi) :
    127 * Real.pi / 180 < gH + gL := by
  have hπ : 0 < Real.pi := Real.pi_pos
  by_cases hr0 : ‖x‖ ≤ 4 / 5
  · have hAH := ah_box_bound x h gH (699 / 1000) (4 / 5)
      (492 * Real.pi / 1800) (653377 / 1000000)
      (by norm_num)
      (by positivity) (by nlinarith [Real.pi_pos])
      hxlo hr0 hhlo hhhi hsepH hcosH hH0 hHpi
      (by
        have heq : 492 * Real.pi / 1800 = 41 * Real.pi / 150 := by ring
        rw [heq]
        exact cos_41pi_div_150_gt_653377ppm)
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
    have hAL := al_box_bound x l gL (699 / 1000) (4 / 5)
      ((783 / 10) * Real.pi / 180) (201 / 1000)
      (by norm_num)
      (by positivity) (by nlinarith [Real.pi_pos])
      hxlo hr0 hllo hlhi hsepL hcosL hL0 hLpi
      cos_deg_783
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
    have hsum : 127 * Real.pi / 180 <
        (492 * Real.pi / 1800) + ((783 / 10) * Real.pi / 180) := by
      nlinarith [hπ]
    linarith
  · by_cases hr1 : ‖x‖ ≤ 9 / 10
    · have hAH := ah_box_bound x h gH (4 / 5) (9 / 10)
        (52 * Real.pi / 180) (615 / 1000)
        (by norm_num)
        (by positivity) (by nlinarith [Real.pi_pos])
        (by linarith) hr1 hhlo hhhi hsepH hcosH hH0 hHpi
        cos_deg_52
        (by norm_num [pairExpr]) (by norm_num [pairExpr])
        (by norm_num [pairExpr]) (by norm_num [pairExpr])
      have hAL := al_box_bound x l gL (4 / 5) (9 / 10)
        ((769 / 10) * Real.pi / 180) (226 / 1000)
        (by norm_num)
        (by positivity) (by nlinarith [Real.pi_pos])
        (by linarith) hr1 hllo hlhi hsepL hcosL hL0 hLpi
        cos_deg_769
        (by norm_num [pairExpr]) (by norm_num [pairExpr])
        (by norm_num [pairExpr]) (by norm_num [pairExpr])
      have hsum : 127 * Real.pi / 180 <
          (52 * Real.pi / 180) + ((769 / 10) * Real.pi / 180) := by
        nlinarith [hπ]
      linarith
    · by_cases hr2 : ‖x‖ ≤ 11 / 10
      · have hAH := ah_box_bound x h gH (9 / 10) (11 / 10)
          ((543 / 10) * Real.pi / 180) (583 / 1000)
          (by norm_num)
          (by positivity) (by nlinarith [Real.pi_pos])
          (by linarith) hr2 hhlo hhhi hsepH hcosH hH0 hHpi
          cos_deg_543
          (by norm_num [pairExpr]) (by norm_num [pairExpr])
          (by norm_num [pairExpr]) (by norm_num [pairExpr])
        have hAL := al_box_bound x l gL (9 / 10) (11 / 10)
          ((735 / 10) * Real.pi / 180) (280 / 1000)
          (by norm_num)
          (by positivity) (by nlinarith [Real.pi_pos])
          (by linarith) hr2 hllo hlhi hsepL hcosL hL0 hLpi
          cos_deg_735
          (by norm_num [pairExpr]) (by norm_num [pairExpr])
          (by norm_num [pairExpr]) (by norm_num [pairExpr])
        have hsum : 127 * Real.pi / 180 <
            ((543 / 10) * Real.pi / 180) + ((735 / 10) * Real.pi / 180) := by
          nlinarith [hπ]
        linarith
      · have hAH := ah_box_bound x h gH (11 / 10) (1301 / 1000)
          ((563 / 10) * Real.pi / 180) (553 / 1000)
          (by norm_num)
          (by positivity) (by nlinarith [Real.pi_pos])
          (by linarith) hxhi hhlo hhhi hsepH hcosH hH0 hHpi
          cos_deg_563
          (by norm_num [pairExpr]) (by norm_num [pairExpr])
          (by norm_num [pairExpr]) (by norm_num [pairExpr])
        have hAL := al_box_bound x l gL (11 / 10) (1301 / 1000)
          ((708 / 10) * Real.pi / 180) (328 / 1000)
          (by norm_num)
          (by positivity) (by nlinarith [Real.pi_pos])
          (by linarith) hxhi hllo hlhi hsepL hcosL hL0 hLpi
          (by
            have heq : (708 / 10) * Real.pi / 180 =
                59 * Real.pi / 150 := by ring
            rw [heq]
            exact cos_59pi_div_150_gt_328permille)
          (by norm_num [pairExpr]) (by norm_num [pairExpr])
          (by norm_num [pairExpr]) (by norm_num [pairExpr])
        have hsum : 127 * Real.pi / 180 <
            ((563 / 10) * Real.pi / 180) + ((708 / 10) * Real.pi / 180) := by
          nlinarith [hπ]
        linarith

end CP15
