import CP15.RationalPairAngle
import CP15.TrigonometricPolynomialBounds

namespace CP15

/-- Cosine lower certificates for the obtuse half of the degree range.
Reflection about pi reduces the proof to a small sine remainder, avoiding
an invalid small-angle Taylor substitution near 180 degrees. -/
theorem cos_obtuse_degrees_lower_of_certificate (k c : ℝ)
    (hk90 : 90 ≤ k) (hk180 : k ≤ 180)
    (hpoly0 : 0 ≤
      (180 - k) * (3141592 / 1000000 : ℝ) / 360 -
      ((180 - k) * (3141593 / 1000000 : ℝ) / 360) ^ 3 / 6 -
      ((180 - k) * (3141593 / 1000000 : ℝ) / 360) ^ 7 / 5040 +
      ((180 - k) * (3141592 / 1000000 : ℝ) / 360) ^ 5 / 120)
    (hcert : c < -1 + 2 *
      ((180 - k) * (3141592 / 1000000 : ℝ) / 360 -
        ((180 - k) * (3141593 / 1000000 : ℝ) / 360) ^ 3 / 6 -
        ((180 - k) * (3141593 / 1000000 : ℝ) / 360) ^ 7 / 5040 +
        ((180 - k) * (3141592 / 1000000 : ℝ) / 360) ^ 5 / 120) ^ 2) :
    c < Real.cos (k * Real.pi / 180) := by
  let x : ℝ := (Real.pi - k * Real.pi / 180) / 2
  let l : ℝ := (180 - k) * (3141592 / 1000000 : ℝ) / 360
  let u : ℝ := (180 - k) * (3141593 / 1000000 : ℝ) / 360
  let lower : ℝ := l - u ^ 3 / 6 - u ^ 7 / 5040 + l ^ 5 / 120
  have hx0 : 0 ≤ x := by dsimp [x]; nlinarith [Real.pi_pos]
  have hl0 : 0 ≤ l := by dsimp [l]; nlinarith
  have hlx : l ≤ x := by dsimp [l, x]; nlinarith [Real.pi_gt_d6]
  have hxu : x ≤ u := by dsimp [u, x]; nlinarith [Real.pi_lt_d6]
  have hsinLo := sin_taylor_seven_lower x hx0
  have hcub : x ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hx0 hxu 3
  have hseventh : x ^ 7 ≤ u ^ 7 := pow_le_pow_left₀ hx0 hxu 7
  have hfifth : l ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ hl0 hlx 5
  have hlower0 : 0 ≤ lower := hpoly0
  have hlowerSin : lower ≤ Real.sin x := by dsimp [lower]; linarith
  have hcos : Real.cos (k * Real.pi / 180) = -1 + 2 * Real.sin x ^ 2 := by
    have heq : k * Real.pi / 180 = Real.pi - 2 * x := by dsimp [x]; ring
    rw [heq, Real.cos_pi_sub, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hcos]
  have hsq : lower ^ 2 ≤ Real.sin x ^ 2 := by nlinarith
  have hcert' : c < -1 + 2 * lower ^ 2 := hcert
  linarith

/-- The same geometric corner checker is valid through 180 degrees.
Its cosine certificate may be supplied by either degree-range lemma. -/
theorem directed_pair_box_angle_gt_full
    (x y : Plane) (g k c rlo rhi slo shi : ℝ)
    (hrlo0 : 0 < rlo) (hslo0 : 0 < slo)
    (hrlo : rlo ≤ ‖x‖) (hrhi : ‖x‖ ≤ rhi)
    (hslo : slo ≤ ‖y‖) (hshi : ‖y‖ ≤ shi)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hk0 : 0 ≤ k) (hk180 : k ≤ 180)
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
  · have hkπ : k * Real.pi / 180 ≤ Real.pi := by nlinarith [Real.pi_pos]
    exact hkπ.trans_lt (lt_of_not_ge hgπ)

end CP15
