import CP15.LocalDerivativeBounds

namespace CP15

/-- A checked mean-value bridge from derivative intervals to errors in
linearized function values. Both endpoints and the whole closed segment
are included in the differentiability and derivative-bound premises. -/
theorem linearization_error_of_derivative_bound
    (f df : ℝ → ℝ) (l u c ε r s : ℝ)
    (hd : ∀ x ∈ Set.Icc l u, HasDerivAt f (df x) x)
    (hbound : ∀ x ∈ Set.Icc l u, |df x - c| ≤ ε)
    (hr : r ∈ Set.Icc l u) (hs : s ∈ Set.Icc l u) :
    |f r - f s - c * (r - s)| ≤ ε * |r - s| := by
  let g : ℝ → ℝ := fun x => f x - c * x
  have hg (x : ℝ) (hx : x ∈ Set.Icc l u) :
      HasDerivWithinAt g (df x - c) (Set.Icc l u) x := by
    convert ((hd x hx).sub ((hasDerivAt_id x).const_mul c)).hasDerivWithinAt using 1 <;>
      simp [g, Pi.sub_def]
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg
    (fun x hx => by simpa [Real.norm_eq_abs] using hbound x hx)
    (convex_Icc l u) hs hr
  have heq : g r - g s = f r - f s - c * (r - s) := by dsimp [g]; ring
  rw [heq, Real.norm_eq_abs, Real.norm_eq_abs] at hh
  exact hh

theorem contactAngle_comm (r s : ℝ) : contactAngle r s = contactAngle s r := by
  unfold contactAngle contactCos
  congr 1
  congr 1 <;> ring

/-- Actual outer-contact angles admit the stated linearization at any
reference radius in the closed local interval. -/
theorem local_outer_angle_linearization (b r s : ℝ)
    (hblo : (35213 / 10000 : ℝ) ≤ b) (hbhi : b ≤ 35214 / 10000)
    (hr : r ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hs : s ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    |contactAngle b r - contactAngle b s - (81 / 100 : ℝ) * (r - s)| ≤
      (2 / 100 : ℝ) * |r - s| := by
  apply linearization_error_of_derivative_bound (contactAngle b)
    (contactAngleDerivative b) _ _ (81 / 100) (2 / 100) r s
  · intro x hx
    have hbox := local_outer_derivative_bounds b x hblo hbhi hx.1 hx.2
    exact hasDerivAt_contactAngle b x (by linarith) (by linarith [hx.1]) hbox.1
  · intro x hx
    have hbox := local_outer_derivative_bounds b x hblo hbhi hx.1 hx.2
    apply abs_le.mpr
    constructor <;> linarith [hbox.2.1, hbox.2.2]
  · exact hr
  · exact hs

/-- The actual inner-pair angle's one-coordinate linearization. -/
theorem local_inner_angle_linearization (fixed r s : ℝ)
    (hfixed : fixed ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hr : r ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hs : s ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    |contactAngle fixed r - contactAngle fixed s + (43 / 100 : ℝ) * (r - s)| ≤
      (1 / 100 : ℝ) * |r - s| := by
  have h := linearization_error_of_derivative_bound (contactAngle fixed)
    (contactAngleDerivative fixed) (1697 / 1000) (853 / 500)
    (-(43 / 100)) (1 / 100) r s
  have hd (x : ℝ) (hx : x ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :=
    local_inner_negative_derivative_bounds x fixed hx.1 hx.2 hfixed.1 hfixed.2
  have hh := h
    (fun x hx => hasDerivAt_contactAngle fixed x (by linarith [hfixed.1])
      (by linarith [hx.1]) (hd x hx).1)
    (fun x hx => abs_le.mpr ⟨by linarith [(hd x hx).2.2],
      by linarith [(hd x hx).2.1]⟩) hr hs
  simpa only [neg_mul, sub_neg_eq_add] using hh

/-- The two-coordinate inner-pair error follows along two coordinate
segments. No unverified multivariable mean-value shortcut is used. -/
theorem local_pair_angle_linearization (r s r₀ : ℝ)
    (hr : r ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (hs : s ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500))
    (h₀ : r₀ ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    |contactAngle s r - contactAngle r₀ r₀ +
      (43 / 100 : ℝ) * ((r - r₀) + (s - r₀))| ≤
      (1 / 100 : ℝ) * (|r - r₀| + |s - r₀|) := by
  have h1 := local_inner_angle_linearization s r r₀ hs hr h₀
  have h2 := local_inner_angle_linearization r₀ s r₀ h₀ hs h₀
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
