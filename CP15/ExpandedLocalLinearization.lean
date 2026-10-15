import CP15.ExpandedLocalDerivativeBounds
import CP15.LocalAngleLinearization

namespace CP15

/-- Actual outer-contact angles admit the stated linearization at any
reference radius in the closed local interval. -/
theorem expanded_outer_angle_linearization (b r s : ℝ)
    (hblo : (35213 / 10000 : ℝ) ≤ b) (hbhi : b ≤ 35214 / 10000)
    (hr : r ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hs : s ∈ Set.Icc (42 / 25 : ℝ) (43 / 25)) :
    |contactAngle b r - contactAngle b s - (81 / 100 : ℝ) * (r - s)| ≤
      (8 / 100 : ℝ) * |r - s| := by
  apply linearization_error_of_derivative_bound (contactAngle b)
    (contactAngleDerivative b) _ _ (81 / 100) (8 / 100) r s
  · intro x hx
    have hbox := expanded_outer_derivative_bounds b x hblo hbhi hx.1 hx.2
    exact hasDerivAt_contactAngle b x (by linarith) (by linarith [hx.1]) hbox.1
  · intro x hx
    have hbox := expanded_outer_derivative_bounds b x hblo hbhi hx.1 hx.2
    apply abs_le.mpr
    constructor <;> linarith [hbox.2.1, hbox.2.2]
  · exact hr
  · exact hs

/-- The actual inner-pair angle's one-coordinate linearization. -/
theorem expanded_inner_angle_linearization (fixed r s : ℝ)
    (hfixed : fixed ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr : r ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hs : s ∈ Set.Icc (42 / 25 : ℝ) (43 / 25)) :
    |contactAngle fixed r - contactAngle fixed s + (43 / 100 : ℝ) * (r - s)| ≤
      (8 / 100 : ℝ) * |r - s| := by
  have h := linearization_error_of_derivative_bound (contactAngle fixed)
    (contactAngleDerivative fixed) (42 / 25) (43 / 25)
    (-(43 / 100)) (8 / 100) r s
  have hd (x : ℝ) (hx : x ∈ Set.Icc (42 / 25 : ℝ) (43 / 25)) :=
    expanded_inner_negative_derivative_bounds x fixed hx.1 hx.2 hfixed.1 hfixed.2
  have hh := h
    (fun x hx => hasDerivAt_contactAngle fixed x (by linarith [hfixed.1])
      (by linarith [hx.1]) (hd x hx).1)
    (fun x hx => abs_le.mpr ⟨by linarith [(hd x hx).2.2],
      by linarith [(hd x hx).2.1]⟩) hr hs
  simpa only [neg_mul, sub_neg_eq_add] using hh

/-- The two-coordinate inner-pair error follows along two coordinate
segments. No unverified multivariable mean-value shortcut is used. -/
theorem expanded_pair_angle_linearization (r s r₀ : ℝ)
    (hr : r ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hs : s ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (h₀ : r₀ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25)) :
    |contactAngle s r - contactAngle r₀ r₀ +
      (43 / 100 : ℝ) * ((r - r₀) + (s - r₀))| ≤
      (8 / 100 : ℝ) * (|r - r₀| + |s - r₀|) := by
  have h1 := expanded_inner_angle_linearization s r r₀ hs hr h₀
  have h2 := expanded_inner_angle_linearization r₀ s r₀ h₀ hs h₀
  have ha := abs_add_le
    (contactAngle s r - contactAngle s r₀ + (43 / 100 : ℝ) * (r - r₀))
    (contactAngle r₀ s - contactAngle r₀ r₀ + (43 / 100 : ℝ) * (s - r₀))
  rw [contactAngle_comm s r₀] at ha h1
  have heq :
      (contactAngle s r - contactAngle r₀ s + (43 / 100 : ℝ) * (r - r₀)) +
      (contactAngle r₀ s - contactAngle r₀ r₀ + (43 / 100 : ℝ) * (s - r₀)) =
      contactAngle s r - contactAngle r₀ r₀ +
        (43 / 100 : ℝ) * ((r - r₀) + (s - r₀)) := by ring
  rw [heq] at ha
  linarith

end CP15
