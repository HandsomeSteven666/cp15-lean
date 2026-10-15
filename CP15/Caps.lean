import CP15.CompactSelection

open scoped InnerProductSpace

namespace CP15

def TouchesOuter {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (i : Fin n) : Prop :=
  ∃ j, j ≠ i ∧ ‖p j‖ = b ∧ dist (p i) (p j) = 2

noncomputable def F (b : ℝ) : ℝ := Real.sqrt (D b ^ 2 - 4)

theorem D_ge_two_of_fodor_radius {b : ℝ}
    (hb : 1 + Real.sqrt 5 ≤ b) : 2 ≤ D b := by
  let a : ℝ := 1 + Real.sqrt 5
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have ha : a ^ 2 - 2 * a - 4 = 0 := by
    dsimp [a]
    nlinarith
  have hba : 0 ≤ b - a := sub_nonneg.mpr hb
  have hsum : 0 ≤ b + a - 2 := by
    dsimp [a]
    nlinarith
  have hpoly : 0 ≤ b ^ 2 - 2 * b - 4 := by
    have hprod := mul_nonneg hba hsum
    nlinarith
  have hb0 : 0 < b := by
    nlinarith
  have hdiv : 4 / b ≤ b - 2 := (div_le_iff₀ hb0).2 (by nlinarith)
  unfold D
  linarith

theorem nonouter_inner_cap_squared {n : ℕ}
    (p : Fin n → Plane) (b : ℝ)
    (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hcap : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (i : Fin n) (hi : ‖p i‖ < b)
    (hnonzero : p i ≠ 0) (hnoouter : ¬TouchesOuter p b i) :
    ‖p i‖ ^ 2 < D b ^ 2 - 4 := by
  obtain ⟨j, hji, hcontact, hdot⟩ := hblock i hi hnonzero
  have hjinner : ‖p j‖ < b := by
    have hjle := hpack.1 j
    by_contra hjnot
    have hjouter : ‖p j‖ = b := le_antisymm hjle (le_of_not_gt hjnot)
    exact hnoouter ⟨j, hji, hjouter, hcontact⟩
  have hjcap := hcap j hjinner
  have hDpos : 0 < D b := D_pos hb
  have hjpos : 0 ≤ ‖p j‖ := norm_nonneg _
  have hsq : ‖p j‖ ^ 2 < D b ^ 2 := by
    have hprod : 0 < (D b - ‖p j‖) * (D b + ‖p j‖) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hcontactcap := blocker_radius_sq (p i) (p j) hcontact hdot
  linarith

theorem D_gt_two_of_nonouter_nonzero {n : ℕ}
    (p : Fin n → Plane) (b : ℝ)
    (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hcap : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (i : Fin n) (hi : ‖p i‖ < b)
    (hnonzero : p i ≠ 0) (hnoouter : ¬TouchesOuter p b i) :
    2 < D b := by
  have hs := nonouter_inner_cap_squared p b hb hpack hcap hblock
    i hi hnonzero hnoouter
  have hDpos := D_pos hb
  nlinarith [sq_nonneg ‖p i‖]

theorem nonouter_F_cap {n : ℕ}
    (p : Fin n → Plane) (b : ℝ)
    (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hcap : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (i : Fin n) (hi : ‖p i‖ < b) (hnoouter : ¬TouchesOuter p b i) :
    ‖p i‖ ≤ F b := by
  by_cases hzero : p i = 0
  · simp [hzero, F, Real.sqrt_nonneg]
  · have hs := nonouter_inner_cap_squared p b hb hpack hcap hblock
        i hi hzero hnoouter
    have hrad : 0 ≤ D b ^ 2 - 4 := by
      nlinarith [sq_nonneg ‖p i‖]
    have hFsquare : F b ^ 2 = D b ^ 2 - 4 := by
      unfold F
      exact Real.sq_sqrt hrad
    have hFnonneg : 0 ≤ F b := Real.sqrt_nonneg _
    have hinonneg : 0 ≤ ‖p i‖ := norm_nonneg _
    nlinarith

theorem exists_selected_with_F_cap {n : ℕ} {b : ℝ}
    (hb : 2 < b) (h : CenterFeasible n b) :
    ∃ p : Fin n → Plane,
      InDisk b p ∧ Separated p 2 ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) := by
  obtain ⟨p, hp, hs, hcap, hblock⟩ :=
    exists_selected_inner_cap_and_blocker hb h
  exact ⟨p, hp, hs, hcap,
    fun i hi hno => nonouter_F_cap p b hb ⟨hp, hs⟩ hcap hblock i hi hno⟩

end CP15
