import CP15.K9ScalarBounds

namespace CP15

open scoped Topology

noncomputable def contactAngle (b r : ℝ) : ℝ := Real.arccos (contactCos b r)

def contactRadicand (b r : ℝ) : ℝ :=
  (4 - (b - r) ^ 2) * ((b + r) ^ 2 - 4)

noncomputable def contactAngleDerivative (b r : ℝ) : ℝ :=
  (b ^ 2 - r ^ 2 - 4) / (r * Real.sqrt (contactRadicand b r))

theorem contactRadicand_identity (b r : ℝ) :
    contactRadicand b r = (2 * b * r) ^ 2 - (b ^ 2 + r ^ 2 - 4) ^ 2 := by
  unfold contactRadicand
  ring

theorem hasDerivAt_contactCos (b r : ℝ) (hb : 0 < b) (hr : 0 < r) :
    HasDerivAt (fun x => contactCos b x)
      ((r ^ 2 - b ^ 2 + 4) / (2 * b * r ^ 2)) r := by
  have hn := ((hasDerivAt_const r (b ^ 2)).add
    ((hasDerivAt_id r).pow 2)).sub_const 4
  have hd := (hasDerivAt_id r).const_mul (2 * b)
  have hquot := hn.div hd (show (2 * b) * r ≠ 0 by positivity)
  convert hquot using 1
  · funext x
    rfl
  · dsimp
    field_simp [ne_of_gt hb, ne_of_gt hr]
    ring

/-- A positive triangle radicand puts the contact cosine strictly inside
the differentiable arccos domain. This includes the domain check omitted
when one treats the contact formula as an angle for arbitrary radii. -/
theorem contactCos_sq_lt_one (b r : ℝ) (hb : 0 < b) (hr : 0 < r)
    (htriangle : 0 < contactRadicand b r) : contactCos b r ^ 2 < 1 := by
  have hd : 0 < 2 * b * r := by positivity
  have hc : contactCos b r * (2 * b * r) = b ^ 2 + r ^ 2 - 4 := by
    unfold contactCos
    field_simp
  have hs : contactCos b r ^ 2 * (2 * b * r) ^ 2 =
      (b ^ 2 + r ^ 2 - 4) ^ 2 := by
    calc
      _ = (contactCos b r * (2 * b * r)) ^ 2 := by ring
      _ = _ := by rw [hc]
  have hid := contactRadicand_identity b r
  have hmul : contactCos b r ^ 2 * (2 * b * r) ^ 2 <
      1 * (2 * b * r) ^ 2 := by nlinarith
  exact (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos hd)).mp hmul

theorem contactRadicand_sqrt_identity (b r : ℝ)
    (hb : 0 < b) (hr : 0 < r) (htriangle : 0 < contactRadicand b r) :
    Real.sqrt (contactRadicand b r) =
      (2 * b * r) * Real.sqrt (1 - contactCos b r ^ 2) := by
  have hc2 := contactCos_sq_lt_one b r hb hr htriangle
  have hc : contactCos b r * (2 * b * r) = b ^ 2 + r ^ 2 - 4 := by
    unfold contactCos
    field_simp
  have hs : contactCos b r ^ 2 * (2 * b * r) ^ 2 =
      (b ^ 2 + r ^ 2 - 4) ^ 2 := by
    calc
      _ = (contactCos b r * (2 * b * r)) ^ 2 := by ring
      _ = _ := by rw [hc]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt htriangle.le,
    Real.sq_sqrt (show 0 ≤ 1 - contactCos b r ^ 2 by linarith)]
  nlinarith [contactRadicand_identity b r]

/-- The actual derivative of the contact-angle function. Specializing
`b = B` gives the outer-contact derivative; specializing `b = s` gives
the inner-pair partial derivative in radius `r`. -/
theorem hasDerivAt_contactAngle (b r : ℝ) (hb : 0 < b) (hr : 0 < r)
    (htriangle : 0 < contactRadicand b r) :
    HasDerivAt (fun x => contactAngle b x) (contactAngleDerivative b r) r := by
  have hc2 := contactCos_sq_lt_one b r hb hr htriangle
  have hm : contactCos b r ≠ -1 := by intro h; rw [h] at hc2; norm_num at hc2
  have hp : contactCos b r ≠ 1 := by intro h; rw [h] at hc2; norm_num at hc2
  have hchain := (Real.hasDerivAt_arccos hm hp).comp r
    (hasDerivAt_contactCos b r hb hr)
  have hsqrtpos : 0 < Real.sqrt (1 - contactCos b r ^ 2) :=
    Real.sqrt_pos.mpr (by linarith)
  convert hchain using 1
  · rfl
  · dsimp [contactAngleDerivative]
    rw [contactRadicand_sqrt_identity b r hb hr htriangle]
    field_simp [ne_of_gt hb, ne_of_gt hr, ne_of_gt hsqrtpos]
    ring

end CP15
