import CP15.M2K9DistinctCoreSum

namespace CP15

/-- Exact rational cosine certificate for angles from zero to ninety
degrees. The pi bounds and the sine remainder are library theorems. -/
theorem cos_degrees_lower_of_certificate (k c : ℝ)
    (hk0 : 0 ≤ k) (hk90 : k ≤ 90)
    (hcert : c < 1 - 2 *
      (k * (3141593 / 1000000 : ℝ) / 360 -
        (k * (3141592 / 1000000 : ℝ) / 360) ^ 3 / 6 +
        (k * (3141593 / 1000000 : ℝ) / 360) ^ 5 / 100) ^ 2) :
    c < Real.cos (k * Real.pi / 180) := by
  let l : ℝ := k * (3141592 / 1000000 : ℝ) / 360
  let u : ℝ := k * (3141593 / 1000000 : ℝ) / 360
  apply cos_gt_of_half_interval _ l u c
  · positivity
  · nlinarith [Real.pi_lt_d6]
  · dsimp [l]; positivity
  · dsimp [l]; nlinarith [Real.pi_gt_d6]
  · dsimp [u]; nlinarith [Real.pi_lt_d6]
  · dsimp [u]; nlinarith
  · exact hcert

/-- A four-corner certificate bounds an actual directed clearance angle.
Large directed gaps are handled by their size, so principal-angle branch
choices are not hidden in the theorem's premises. -/
theorem directed_pair_box_angle_gt
    (x y : Plane) (g k c rlo rhi slo shi : ℝ)
    (hrlo0 : 0 < rlo) (hslo0 : 0 < slo)
    (hrlo : rlo ≤ ‖x‖) (hrhi : ‖x‖ ≤ rhi)
    (hslo : slo ≤ ‖y‖) (hshi : ‖y‖ ≤ shi)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hk0 : 0 ≤ k) (hk90 : k ≤ 90)
    (hc : c < Real.cos (k * Real.pi / 180))
    (hll : pairExpr rlo slo c < 4) (hlh : pairExpr rlo shi c < 4)
    (hhl : pairExpr rhi slo c < 4) (hhh : pairExpr rhi shi c < 4) :
    k * Real.pi / 180 < g := by
  by_cases hgπ : g ≤ Real.pi
  · have hbox := pairExpr_lt_four_of_corners rlo ‖x‖ rhi slo ‖y‖ shi c
      hrlo hrhi hslo hshi hll hlh hhl hhh
    have hpoly : ‖x‖ ^ 2 + ‖y‖ ^ 2 - 4 < 2 * c * ‖x‖ * ‖y‖ := by
      dsimp [pairExpr] at hbox
      nlinarith
    exact polar_pair_angle_gt_of_poly x y g c (k * Real.pi / 180)
      (hrlo0.trans_le hrlo) (hslo0.trans_le hslo)
      hsep hpoly hcos hg0 hgπ (by positivity) (by nlinarith [Real.pi_pos]) hc
  · have hkπ : k * Real.pi / 180 < Real.pi := by nlinarith [Real.pi_pos]
    exact hkπ.trans (lt_of_not_ge hgπ)

/-- Two corner-certified angle bounds sharing the same core-radius cell.
This avoids an unproved concavity shortcut in the final distinct branch. -/
theorem coupled_pair_box_angle_sum_gt
    (x y z : Plane) (g h total rlo rhi slo shi tlo thi k₁ k₂ c₁ c₂ : ℝ)
    (hrlo0 : 0 < rlo) (hslo0 : 0 < slo) (htlo0 : 0 < tlo)
    (hrlo : rlo ≤ ‖x‖) (hrhi : ‖x‖ ≤ rhi)
    (hslo : slo ≤ ‖y‖) (hshi : ‖y‖ ≤ shi)
    (htlo : tlo ≤ ‖z‖) (hthi : ‖z‖ ≤ thi)
    (hsepY : 2 ≤ dist x y) (hsepZ : 2 ≤ dist x z)
    (hcosY : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hcosZ : Real.cos (polarArg x - polarArg z) = Real.cos h)
    (hg0 : 0 ≤ g) (hh0 : 0 ≤ h)
    (hk₁0 : 0 ≤ k₁) (hk₁90 : k₁ ≤ 90) (hk₂0 : 0 ≤ k₂) (hk₂90 : k₂ ≤ 90)
    (hc₁ : c₁ < Real.cos (k₁ * Real.pi / 180))
    (hc₂ : c₂ < Real.cos (k₂ * Real.pi / 180))
    (hyll : pairExpr rlo slo c₁ < 4) (hylh : pairExpr rlo shi c₁ < 4)
    (hyhl : pairExpr rhi slo c₁ < 4) (hyhh : pairExpr rhi shi c₁ < 4)
    (hzll : pairExpr rlo tlo c₂ < 4) (hzlh : pairExpr rlo thi c₂ < 4)
    (hzhl : pairExpr rhi tlo c₂ < 4) (hzhh : pairExpr rhi thi c₂ < 4)
    (hdegrees : total < k₁ + k₂) : total * Real.pi / 180 < g + h := by
  have hY := directed_pair_box_angle_gt x y g k₁ c₁ rlo rhi slo shi
    hrlo0 hslo0 hrlo hrhi hslo hshi hsepY hcosY hg0 hk₁0 hk₁90 hc₁
    hyll hylh hyhl hyhh
  have hZ := directed_pair_box_angle_gt x z h k₂ c₂ rlo rhi tlo thi
    hrlo0 htlo0 hrlo hrhi htlo hthi hsepZ hcosZ hh0 hk₂0 hk₂90 hc₂
    hzll hzlh hzhl hzhh
  nlinarith [Real.pi_pos]

end CP15
