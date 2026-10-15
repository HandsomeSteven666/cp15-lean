import CP15.SevenTouchingAngles
import CP15.TrigonometricPolynomialBounds

namespace CP15

/-- A tight rational half-angle cosine bound. Only exact polynomial
inequalities are needed when replaying a numerical table entry. -/
theorem cos_radians_lower_of_certificate (k c : ℝ)
    (hk0 : 0 ≤ k) (hk2 : k ≤ 2)
    (hcert : c < 1 - 2 * (k / 2 - (k / 2) ^ 3 / 6 + (k / 2) ^ 5 / 120) ^ 2) :
    c < Real.cos k := by
  have hs0 : 0 ≤ Real.sin (k / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_gt_three])
  have hsHi := sin_taylor_five_upper (k / 2) (by linarith)
  have hp0 : 0 ≤ k / 2 - (k / 2) ^ 3 / 6 + (k / 2) ^ 5 / 120 := hs0.trans hsHi
  have hsq : Real.sin (k / 2) ^ 2 ≤
      (k / 2 - (k / 2) ^ 3 / 6 + (k / 2) ^ 5 / 120) ^ 2 := by
    nlinarith
  have hc : Real.cos k = 1 - 2 * Real.sin (k / 2) ^ 2 := by
    have hdouble := Real.cos_two_mul (k / 2)
    have hunit := Real.sin_sq_add_cos_sq (k / 2)
    have heq : 2 * (k / 2) = k := by ring
    rw [heq] at hdouble
    nlinarith
  rw [hc]
  linarith

theorem directed_pair_box_radian_gt
    (x y : Plane) (g k c rlo rhi slo shi : ℝ)
    (hrlo0 : 0 < rlo) (hslo0 : 0 < slo)
    (hrlo : rlo ≤ ‖x‖) (hrhi : ‖x‖ ≤ rhi)
    (hslo : slo ≤ ‖y‖) (hshi : ‖y‖ ≤ shi)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hk0 : 0 ≤ k) (hk2 : k ≤ 2)
    (hc : c < Real.cos k)
    (hll : pairExpr rlo slo c < 4) (hlh : pairExpr rlo shi c < 4)
    (hhl : pairExpr rhi slo c < 4) (hhh : pairExpr rhi shi c < 4) : k < g := by
  by_cases hgπ : g ≤ Real.pi
  · have hbox := pairExpr_lt_four_of_corners rlo ‖x‖ rhi slo ‖y‖ shi c
      hrlo hrhi hslo hshi hll hlh hhl hhh
    have hpoly : ‖x‖ ^ 2 + ‖y‖ ^ 2 - 4 < 2 * c * ‖x‖ * ‖y‖ := by
      dsimp [pairExpr] at hbox
      nlinarith
    exact polar_pair_angle_gt_of_poly x y g c k (hrlo0.trans_le hrlo) (hslo0.trans_le hslo)
      hsep hpoly hcos hg0 hgπ hk0 (by linarith [Real.pi_gt_three]) hc
  · linarith [Real.pi_gt_three]

end CP15
