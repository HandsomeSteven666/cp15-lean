import CP15.PolarOrder
import CP15.PolarContact

namespace CP15

/-- A separated family in an annulus narrower than the clearance distance
has distinct polar directions. This applies to any finite family size. -/
theorem annular_polarArg_injective {n : ℕ} (q : Fin n → Plane)
    (hsep : Separated q 2) (lo hi : ℝ) (hwidth : hi - lo < 2)
    (hlo : ∀ i, lo ≤ ‖q i‖) (hhi : ∀ i, ‖q i‖ ≤ hi) :
    Function.Injective (fun i => polarArg (q i)) := by
  intro i j harg
  change polarArg (q i) = polarArg (q j) at harg
  by_contra hij
  have hd := hsep i j hij
  have hdsq : (4 : ℝ) ≤ dist (q i) (q j) ^ 2 := by
    nlinarith [dist_nonneg (x := q i) (y := q j)]
  rw [dist_eq_norm, norm_sub_sq_real, polar_inner, harg, sub_self, Real.cos_zero] at hdsq
  have hdlo : -2 < ‖q i‖ - ‖q j‖ := by linarith [hlo i, hhi j]
  have hdhi : ‖q i‖ - ‖q j‖ < 2 := by linarith [hhi i, hlo j]
  have hp : 0 < (2 + (‖q i‖ - ‖q j‖)) * (2 - (‖q i‖ - ‖q j‖)) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

/-- One full turn split into actual consecutive angular increments.
The final increment includes the polar branch cut. -/
noncomputable def cyclicAngleGap {n : ℕ} (φ : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  φ (i + 1) - φ i + if i = Fin.last n then 2 * Real.pi else 0

theorem cyclicAngleGap_sum {n : ℕ} (φ : Fin (n + 1) → ℝ) :
    (∑ i, cyclicAngleGap φ i) = 2 * Real.pi := by
  have hrotate := Equiv.sum_comp (finRotate (n + 1)) φ
  simp only [finRotate_apply] at hrotate
  simp only [cyclicAngleGap, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hrotate]
  simp

theorem cyclicAngleGap_nonneg {n : ℕ} (φ : Fin (n + 1) → ℝ)
    (hmono : StrictMono φ) (hrange : ∀ i, -Real.pi < φ i ∧ φ i ≤ Real.pi)
    (i : Fin (n + 1)) : 0 ≤ cyclicAngleGap φ i := by
  by_cases hi : i = Fin.last n
  · subst i
    simp only [cyclicAngleGap, ite_true, Fin.last_add_one]
    linarith [(hrange 0).1, (hrange (Fin.last n)).2]
  · have hiLt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
    have hsucc : i < i + 1 := by
      change i.val < (i + 1).val
      rw [Fin.val_add_one_of_lt hiLt]
      omega
    simp only [cyclicAngleGap, if_neg hi, add_zero]
    exact sub_nonneg.mpr (hmono.monotone hsucc.le)

theorem cyclicAngleGap_cos {n : ℕ} (q : Fin (n + 1) → Plane)
    (φ : Fin (n + 1) → ℝ) (harg : ∀ i, polarArg (q i) = φ i)
    (i : Fin (n + 1)) :
    Real.cos (polarArg (q i) - polarArg (q (i + 1))) =
      Real.cos (cyclicAngleGap φ i) := by
  rw [harg i, harg (i + 1)]
  by_cases hi : i = Fin.last n
  · simp only [cyclicAngleGap, if_pos hi]
    rw [Real.cos_add_two_pi, ← Real.cos_neg (φ (i + 1) - φ i)]
    congr 1
    ring
  · simp only [cyclicAngleGap, if_neg hi, add_zero]
    rw [← Real.cos_neg (φ (i + 1) - φ i)]
    congr 1
    ring

end CP15
