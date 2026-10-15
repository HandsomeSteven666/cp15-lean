import CP15.M2K9DistinctStrongBudget
import CP15.RationalWideAngle

namespace CP15

theorem blocker_radius_ge_lower_root (r s l sl : ℝ)
    (hl0 : 0 ≤ l) (hlr : l ≤ r) (hs0 : 0 ≤ s) (hsl0 : 0 ≤ sl)
    (hblocker : 4 + r ^ 2 < s ^ 2) (hroot : sl ^ 2 ≤ 4 + l ^ 2) : sl ≤ s := by
  have hrsq : l ^ 2 ≤ r ^ 2 := by nlinarith
  nlinarith

/-- Two exact lower-offset certificates cannot exceed the actual charged
outer-gap budget. The caller supplies rational corner proofs and the exact
strict sum; no search-program result is accepted as a premise. -/
theorem two_contact_rational_support_impossible
    (b s z d e sl zl a c : ℝ)
    (hb : 3 < b) (hbB : b ≤ (352136 / 100000 : ℝ))
    (hsl0 : 0 < sl) (hzl0 : 0 < zl)
    (hsl : sl ≤ s) (hsU : s ≤ 12 / 5) (hzl : zl ≤ z) (hzU : z ≤ 12 / 5)
    (hd0 : 0 ≤ d) (hdπ : d ≤ Real.pi) (he0 : 0 ≤ e) (heπ : e ≤ Real.pi)
    (hdlaw : 2 * s * b * Real.cos d = b ^ 2 + s ^ 2 - 4)
    (helaw : 2 * z * b * Real.cos e = b ^ 2 + z ^ 2 - 4)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hacert : contactCos (352136 / 100000) sl < 1 - 2 * sinCubicUpper (a / 2) ^ 2)
    (hccert : contactCos (352136 / 100000) zl < 1 - 2 * sinCubicUpper (c / 2) ^ 2)
    (hsum : 2 * a + 2 * c + 7 * (57588 / 100000 : ℝ) >
      2 * (3141593 / 1000000 : ℝ))
    (hbudget : 2 * d + 2 * e + 7 * (57588 / 100000 : ℝ) ≤ 2 * Real.pi) : False := by
  have hd := contact_offset_gt_rational_angle b (352136 / 100000) sl s d a
    hb hbB (by norm_num) hsl0 hsl hsU hd0 hdπ ha0 ha1 hacert hdlaw
  have he := contact_offset_gt_rational_angle b (352136 / 100000) zl z e c
    hb hbB (by norm_num) hzl0 hzl hzU he0 heπ hc0 hc1 hccert helaw
  linarith [Real.pi_lt_d6]

end CP15
