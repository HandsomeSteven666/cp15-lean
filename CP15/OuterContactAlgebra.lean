import CP15.Radial

open scoped InnerProductSpace

namespace CP15

/-- The exact polynomial behind the contact-angle comparison. It has no
trigonometric or cyclic-order premise. -/
theorem contact_alignment_factor (b s : ℝ) (hb : 0 < b) :
    b * (s - b) * (s - D b) =
      b * (b ^ 2 + s ^ 2 - 4) - 2 * s * (b ^ 2 - 2) := by
  unfold D
  field_simp [ne_of_gt hb]
  ring

/-- A contact at an inner radius strictly below `D b` has angular offset
strictly smaller than the boundary separation-two offset, written as a
polynomial inequality. -/
theorem contact_alignment_strict (b s : ℝ) (hb : 0 < b)
    (hs : s < D b) :
    2 * s * (b ^ 2 - 2) < b * (b ^ 2 + s ^ 2 - 4) := by
  have hDb : D b < b := by
    unfold D
    have hdiv : 0 < 4 / b := by positivity
    linarith
  have hprod : 0 < b * (s - b) * (s - D b) := by
    have h1 : s - b < 0 := by linarith
    have h2 : s - D b < 0 := by linarith
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hb h1) h2
  rw [contact_alignment_factor b s hb] at hprod
  linarith

/-- At inner radius at least two, the contact offset has cosine at most
`b/4`. This exact algebraic form avoids an inverse-trigonometric premise.
The inequality is strict if the inner radius is strictly above two. -/
theorem contact_offset_cos_le_b_div_four (b s δ : ℝ)
    (hb : 2 < b) (hs : 2 ≤ s) (hsD : s < D b)
    (hlaw : 2 * s * b * Real.cos δ = b ^ 2 + s ^ 2 - 4) :
    Real.cos δ ≤ b / 4 := by
  have hidentity : b * (b ^ 2 - 2 * D b - 4) =
      (b - 2) ^ 2 * (b + 2) := by
    unfold D
    field_simp [ne_of_gt (by linarith : 0 < b)]
    ring
  have hpositive : 0 < (b - 2) ^ 2 * (b + 2) :=
    mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have hDb : 2 * D b + 4 < b ^ 2 := by
    nlinarith [hidentity]
  have hmargin : 0 < b ^ 2 - 2 * s - 4 := by linarith
  have hproduct : 0 ≤ (s - 2) * (b ^ 2 - 2 * s - 4) :=
    mul_nonneg (by linarith) hmargin.le
  have hscale : 0 < 2 * s * b := by positivity
  nlinarith [hproduct]

theorem contact_offset_cos_lt_b_div_four (b s δ : ℝ)
    (hb : 2 < b) (hs : 2 < s) (hsD : s < D b)
    (hlaw : 2 * s * b * Real.cos δ = b ^ 2 + s ^ 2 - 4) :
    Real.cos δ < b / 4 := by
  have hidentity : b * (b ^ 2 - 2 * D b - 4) =
      (b - 2) ^ 2 * (b + 2) := by
    unfold D
    field_simp [ne_of_gt (by linarith : 0 < b)]
    ring
  have hpositive : 0 < (b - 2) ^ 2 * (b + 2) :=
    mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have hDb : 2 * D b + 4 < b ^ 2 := by
    nlinarith [hidentity]
  have hmargin : 0 < b ^ 2 - 2 * s - 4 := by linarith
  have hproduct : 0 < (s - 2) * (b ^ 2 - 2 * s - 4) :=
    mul_pos (by linarith) hmargin
  have hscale : 0 < 2 * s * b := by positivity
  nlinarith [hproduct]

theorem contact_inner_formula (x z : Plane) (b s : ℝ)
    (hx : ‖x‖ = s) (hz : ‖z‖ = b)
    (hcontact : dist x z = 2) :
    2 * ⟪x, z⟫_ℝ = b ^ 2 + s ^ 2 - 4 := by
  have hsq : ‖x - z‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hcontact]
    norm_num
  rw [norm_sub_sq_real, hx, hz] at hsq
  linarith

theorem outer_pair_inner_upper (z w : Plane) (b : ℝ)
    (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hsep : 2 ≤ dist z w) :
    ⟪z, w⟫_ℝ ≤ b ^ 2 - 2 := by
  have hdsq : 4 ≤ dist z w ^ 2 := by
    have hn : 0 ≤ dist z w := dist_nonneg
    nlinarith
  rw [dist_eq_norm, norm_sub_sq_real, hz, hw] at hdsq
  linarith

/-- Among points on the same outer circle, a contacted center maximizes the
inner product with the given inner center. Equality allows multiple contacts. -/
theorem contact_outer_dot_max (x z w : Plane) (b : ℝ)
    (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hcontact : dist x z = 2) (hsep : 2 ≤ dist x w) :
    ⟪x, w⟫_ℝ ≤ ⟪x, z⟫_ℝ := by
  have hcontact_sq : dist x z ^ 2 = 4 := by rw [hcontact]; norm_num
  have hsep_sq : 4 ≤ dist x w ^ 2 := by
    have hn : 0 ≤ dist x w := dist_nonneg
    nlinarith
  rw [dist_eq_norm, norm_sub_sq_real, hz] at hcontact_sq
  rw [dist_eq_norm, norm_sub_sq_real, hw] at hsep_sq
  linarith

/-- Any inner-outer contact from the strict radial cap is closer in cosine
to its outer endpoint than any separated pair of outer centers. This is only
an alignment inequality; adjacency still requires an oriented ring order. -/
theorem contact_closer_than_outer_pair (x z w : Plane) (b s : ℝ)
    (hb : 0 < b) (hs : 0 ≤ s) (hsD : s < D b)
    (hx : ‖x‖ = s) (hz : ‖z‖ = b) (hw : ‖w‖ = b)
    (hcontact : dist x z = 2) (houter_sep : 2 ≤ dist z w) :
    s * ⟪z, w⟫_ℝ < b * ⟪x, z⟫_ℝ := by
  have halign := contact_alignment_strict b s hb hsD
  have hformula := contact_inner_formula x z b s hx hz hcontact
  have houter := outer_pair_inner_upper z w b hz hw houter_sep
  have hscaled := mul_le_mul_of_nonneg_left houter hs
  nlinarith

/-- Algebraic data for an inner center contacting one boundary center in a
packing. The second boundary center is arbitrary. This theorem makes no
assumption about which cyclic gap contains the inner center. -/
theorem inner_outer_contact_order_data {n : ℕ}
    (p : Fin n → Plane) (b : ℝ) (hb : 0 < b)
    (hsep : Separated p 2)
    (hD : ∀ q, ‖p q‖ < b → ‖p q‖ < D b)
    (i j k : Fin n) (hinner : ‖p i‖ < b)
    (hj : ‖p j‖ = b) (hk : ‖p k‖ = b)
    (hcontact : dist (p i) (p j) = 2)
    (hjk : j ≠ k) (hik : i ≠ k) :
    ‖p i‖ * ⟪p j, p k⟫_ℝ < b * ⟪p i, p j⟫_ℝ ∧
      ⟪p i, p k⟫_ℝ ≤ ⟪p i, p j⟫_ℝ := by
  constructor
  · exact contact_closer_than_outer_pair (p i) (p j) (p k)
      b ‖p i‖ hb (norm_nonneg _) (hD i hinner)
      rfl hj hk hcontact (hsep j k hjk)
  · exact contact_outer_dot_max (p i) (p j) (p k) b
      hj hk hcontact (hsep i k hik)

end CP15
