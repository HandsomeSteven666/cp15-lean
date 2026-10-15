import CP15.RationalRadianAngle

namespace CP15

set_option maxHeartbeats 0

theorem cos_taylor_eight_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  let f : ℝ → ℝ := fun t => Real.cos t -
    (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320)
  have hd (t : ℝ) : deriv f t =
      -Real.sin t + t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 := by
    simp (disch := fun_prop) [f]
    ring
  have hm : AntitoneOn f (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    rw [hd]
    linarith [sin_taylor_seven_lower t ht'.le]
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at h
  exact sub_nonpos.mp h

theorem sin_taylor_nine_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 := by
  let f : ℝ → ℝ := fun t =>
    t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - Real.sin t
  have hd (t : ℝ) : deriv f t =
      1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    rw [hd]
    linarith [cos_taylor_eight_upper t ht'.le]
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero] at h
  exact sub_nonneg.mp h

noncomputable def sinNineUpper (t : ℝ) : ℝ :=
  t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880

/-- Full minor-angle domain, including obtuse angles. The half-angle
identity has a proved positive sine and a global polynomial remainder. -/
theorem cos_full_radians_lower_of_certificate (k c : ℝ)
    (hk0 : 0 ≤ k) (hkπ : k ≤ Real.pi)
    (hcert : c < 1 - 2 * sinNineUpper (k / 2) ^ 2) : c < Real.cos k := by
  have hs0 : 0 ≤ Real.sin (k / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsHi : Real.sin (k / 2) ≤ sinNineUpper (k / 2) :=
    sin_taylor_nine_upper _ (by linarith)
  have hp0 : 0 ≤ sinNineUpper (k / 2) := hs0.trans hsHi
  have hsq : Real.sin (k / 2) ^ 2 ≤ sinNineUpper (k / 2) ^ 2 := by nlinarith
  have hc : Real.cos k = 1 - 2 * Real.sin (k / 2) ^ 2 := by
    have hd := Real.cos_two_mul (k / 2)
    have hu := Real.sin_sq_add_cos_sq (k / 2)
    have heq : 2 * (k / 2) = k := by ring
    rw [heq] at hd
    nlinarith
  rw [hc]
  linarith

theorem directed_pair_box_full_radian_gt
    (x y : Plane) (g k c rlo rhi slo shi : ℝ)
    (hrlo0 : 0 < rlo) (hslo0 : 0 < slo)
    (hrlo : rlo ≤ ‖x‖) (hrhi : ‖x‖ ≤ rhi)
    (hslo : slo ≤ ‖y‖) (hshi : ‖y‖ ≤ shi)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) (hk0 : 0 ≤ k) (hkπ : k ≤ Real.pi)
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
      hsep hpoly hcos hg0 hgπ hk0 hkπ hc
  · exact hkπ.trans_lt (lt_of_not_ge hgπ)

end CP15
