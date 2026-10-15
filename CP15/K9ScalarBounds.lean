import CP15.ParametricOuterGap
import CP15.SharedBlockerThirdRadius

namespace CP15

noncomputable def contactCos (b s : ℝ) : ℝ :=
  (b ^ 2 + s ^ 2 - 4) / (2 * b * s)

private theorem contactCos_mono_b (b B s : ℝ)
    (hb : 0 < b) (hbB : b ≤ B) (hB : 0 < B)
    (hs : 0 < s) (hsupper : s ≤ 12 / 5)
    (hb3 : 3 < b) : contactCos b s ≤ contactCos B s := by
  have hfactor : 0 ≤ (B - b) * (B * b - s ^ 2 + 4) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hscale := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * s) hfactor
  unfold contactCos
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * b * s)
    (by positivity : 0 < 2 * B * s)).2
  nlinarith

private theorem contactCos_anti_s (B l s : ℝ)
    (hB : 0 < B) (hBsq : 12 < B ^ 2)
    (hl : 0 < l) (hls : l ≤ s)
    (hs : 0 < s) (hsupper : s ≤ 12 / 5) :
    contactCos B s ≤ contactCos B l := by
  have hlupper : l ≤ 12 / 5 := by linarith
  have hfactor : 0 ≤ (s - l) * (B ^ 2 - 4 - l * s) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hscale := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * B) hfactor
  unfold contactCos
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * B * s)
    (by positivity : 0 < 2 * B * l)).2
  nlinarith

/-- A monotone rational upper enclosure for the cosine of any contact
offset at radius at least `l`. -/
theorem contact_offset_cos_le_rational_corner
    (b B l s δ : ℝ)
    (hb3 : 3 < b) (hbB : b ≤ B) (hBsq : 12 < B ^ 2)
    (hl : 0 < l) (hls : l ≤ s) (hsupper : s ≤ 12 / 5)
    (hlaw : 2 * s * b * Real.cos δ = b ^ 2 + s ^ 2 - 4) :
    Real.cos δ ≤ contactCos B l := by
  have hb : 0 < b := by linarith
  have hB : 0 < B := by linarith
  have hs : 0 < s := by linarith
  have hcos : Real.cos δ = contactCos b s := by
    unfold contactCos
    apply (eq_div_iff (by positivity : (0 : ℝ) < 2 * b * s).ne').2
    nlinarith [hlaw]
  rw [hcos]
  exact (contactCos_mono_b b B s hb hbB hB hs hsupper hb3).trans
    (contactCos_anti_s B l s hB hBsq hl hls hs hsupper)

noncomputable def sinCubicUpper (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 100

/-- A rational polynomial lower enclosure for cosine on `[0,1]`,
derived from the checked cubic sine remainder. -/
theorem cos_lower_from_sin_cubic (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 - 2 * sinCubicUpper (θ / 2) ^ 2 ≤ Real.cos θ := by
  let x := θ / 2
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_gt_three])
  have hbound := Real.sin_bound (x := x) (by simpa [abs_of_nonneg hx0] using hx1)
  have hsinupper : Real.sin x ≤ sinCubicUpper x := by
    have h := (abs_le.mp hbound).2
    rw [abs_of_nonneg hx0] at h
    dsimp [sinCubicUpper]
    linarith
  have hpoly0 : 0 ≤ sinCubicUpper x := le_trans hsin0 hsinupper
  have hsq : Real.sin x ^ 2 ≤ sinCubicUpper x ^ 2 := by
    nlinarith [mul_nonneg hsin0 (sub_nonneg.mpr hsinupper),
      mul_nonneg hpoly0 (sub_nonneg.mpr hsinupper)]
  have hcosid : Real.cos θ = 1 - 2 * Real.sin x ^ 2 := by
    have htwo := Real.cos_two_mul x
    have hsumsq := Real.sin_sq_add_cos_sq x
    have hdouble : 2 * x = θ := by dsimp [x]; ring
    rw [hdouble] at htwo
    nlinarith
  rw [hcosid]
  dsimp [x] at hsq ⊢
  linarith

/-- A single rational corner test turns a cosine-law offset into a
certified rational angular lower bound. -/
theorem contact_offset_gt_rational_angle
    (b B l s δ θ : ℝ)
    (hb3 : 3 < b) (hbB : b ≤ B) (hBsq : 12 < B ^ 2)
    (hl : 0 < l) (hls : l ≤ s) (hsupper : s ≤ 12 / 5)
    (hδ0 : 0 ≤ δ) (hδpi : δ ≤ Real.pi)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hcorner : contactCos B l <
      1 - 2 * sinCubicUpper (θ / 2) ^ 2)
    (hlaw : 2 * s * b * Real.cos δ = b ^ 2 + s ^ 2 - 4) :
    θ < δ := by
  have hcosupper := contact_offset_cos_le_rational_corner b B l s δ
    hb3 hbB hBsq hl hls hsupper hlaw
  have hcoslower := cos_lower_from_sin_cubic θ hθ0 hθ1
  by_contra hnot
  have hδθ : δ ≤ θ := le_of_not_gt hnot
  have hcosmono := Real.cos_le_cos_of_nonneg_of_le_pi hδ0
    (by linarith [Real.pi_gt_three] : θ ≤ Real.pi) hδθ
  linarith

/-- One exact rational interval cell for the correlated two-contact
budget. The premises `hcorner*`, `hzcorner`, and `hangles` are polynomial
rational inequalities checked separately for each saved cell. -/
theorem k9_scalar_bin_contradiction
    (b s z r δ₁ δ₂ l u zlo θ₁ θ₂ : ℝ)
    (hb3 : 3 < b) (hbB : b ≤ (352136 / 100000 : ℝ))
    (hb12 : 12 < b ^ 2)
    (hs2 : 2 < s) (hl2 : 2 < l) (hslo : l ≤ s) (hshi : s ≤ u)
    (hu2 : 2 < u) (huhi : u ≤ 12 / 5)
    (hz2 : 2 < z) (hzhi : z ≤ 12 / 5)
    (hrlower : 8 / s - s < r)
    (hzsq : 4 + r ^ 2 < z ^ 2)
    (hzlo : 2 < zlo)
    (hzcorner : zlo ^ 2 < 4 + (8 / u - u) ^ 2)
    (hδ₁0 : 0 ≤ δ₁) (hδ₁pi : δ₁ ≤ Real.pi)
    (hδ₂0 : 0 ≤ δ₂) (hδ₂pi : δ₂ ≤ Real.pi)
    (hlaw₁ : 2 * s * b * Real.cos δ₁ = b ^ 2 + s ^ 2 - 4)
    (hlaw₂ : 2 * z * b * Real.cos δ₂ = b ^ 2 + z ^ 2 - 4)
    (hθ₁ : 0 ≤ θ₁ ∧ θ₁ ≤ 1)
    (hθ₂ : 0 ≤ θ₂ ∧ θ₂ ≤ 1)
    (hcorner₁ : contactCos (352136 / 100000) l <
      1 - 2 * sinCubicUpper (θ₁ / 2) ^ 2)
    (hcorner₂ : contactCos (352136 / 100000) zlo <
      1 - 2 * sinCubicUpper (θ₂ / 2) ^ 2)
    (hangles : 2 * θ₁ + 2 * θ₂ + 7 * (57588 / 100000 : ℝ) >
      2 * (3141593 / 1000000 : ℝ))
    (hbudget : 2 * δ₁ + 2 * δ₂ + 7 * (57588 / 100000 : ℝ) ≤
      2 * Real.pi) : False := by
  have hspos : 0 < s := by linarith
  have hupos : 0 < u := by linarith
  have hRupos : 0 < 8 / u - u := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hupos).2
    nlinarith
  have hRmono : 8 / u - u ≤ 8 / s - s := by
    have hdiv : 8 / u ≤ 8 / s := by
      apply (div_le_div_iff₀ hupos hspos).2
      nlinarith
    linarith
  have hrpos : 0 < r := by linarith
  have hzlower : zlo ≤ z := by
    nlinarith [norm_nonneg (0 : Plane)]
  have hδ₁ : θ₁ < δ₁ :=
    contact_offset_gt_rational_angle b (352136 / 100000) l s δ₁ θ₁
      hb3 hbB (by norm_num) (by linarith) hslo
      (by linarith) hδ₁0 hδ₁pi hθ₁.1 hθ₁.2 hcorner₁ hlaw₁
  have hδ₂ : θ₂ < δ₂ :=
    contact_offset_gt_rational_angle b (352136 / 100000) zlo z δ₂ θ₂
      hb3 hbB (by norm_num) (by linarith) hzlower hzhi
      hδ₂0 hδ₂pi hθ₂.1 hθ₂.2 hcorner₂ hlaw₂
  have hpi : Real.pi < (3141593 / 1000000 : ℝ) := by
    linarith [Real.pi_lt_d6]
  linarith

end CP15
