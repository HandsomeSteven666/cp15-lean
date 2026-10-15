import CP15.NonOuterStructure

open scoped InnerProductSpace

namespace CP15

/-- The algebraic radius consequence of the strict three-point cap. -/
theorem radius_gt_two_sqrt_three_of_F_sq (b : ℝ) (hb : 2 < b)
    (hF : 4 / 3 < F b ^ 2) :
    2 * Real.sqrt 3 < b := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hDpos : 0 < D b := D_pos hb
  have hrad : 0 ≤ D b ^ 2 - 4 := by
    by_contra hnot
    have hzero : F b = 0 := by
      unfold F
      exact Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hnot)
    rw [hzero] at hF
    norm_num at hF
  have hFsq : F b ^ 2 = D b ^ 2 - 4 := by
    unfold F
    exact Real.sq_sqrt hrad
  have hDsq : 16 / 3 < D b ^ 2 := by linarith
  let q : ℝ := 2 * Real.sqrt 3
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hDq : D q = 4 / 3 * Real.sqrt 3 := by
    dsimp [q, D]
    field_simp
    nlinarith
  have hDqsq : D q ^ 2 = 16 / 3 := by
    rw [hDq]
    nlinarith
  by_contra hnot
  have hbq : b ≤ q := le_of_not_gt hnot
  have hrec : 4 / q ≤ 4 / b := by
    apply (div_le_div_iff₀ hqpos (by linarith)).2
    nlinarith
  have hDle : D b ≤ D q := by
    unfold D
    linarith
  have hDqpos : 0 ≤ D q := by
    rw [hDq]
    positivity
  nlinarith

/-- Three non-outer centers in a selected packing force the strict
`m = 3` radius cutoff. The finite-index extraction is complete. -/
theorem m3_radius_cutoff (p : Fin 15 → Plane) (b : ℝ) (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ q, ‖p q‖ < b → ‖p q‖ < D b)
    (hblock : ∀ q, ‖p q‖ < b → p q ≠ 0 →
      ∃ j, j ≠ q ∧ dist (p q) (p j) = 2 ∧
        ‖p q‖ ^ 2 < ⟪p j, p q⟫_ℝ)
    (hFcap : ∀ q, ‖p q‖ < b → ¬TouchesOuter p b q → ‖p q‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hm3 : 3 ≤ (nonOuterIndices p b).card) :
    2 * Real.sqrt 3 < b := by
  classical
  have hthree : Fintype.card (Fin 3) ≤ (nonOuterIndices p b).card := by
    simpa using hm3
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hthree
  have hmem (a : Fin 3) :
      ‖p (e a)‖ < b ∧ ¬TouchesOuter p b (e a) := by
    have ha : e a ∈ nonOuterIndices p b := he ⟨a, rfl⟩
    simpa [nonOuterIndices] using ha
  have hFstrict := three_nonOuter_F_sq_gt_four_thirds p b hb hpack
    hD hblock hFcap hFsmall (e 0) (e 1) (e 2)
    (e.injective.ne (by decide))
    (e.injective.ne (by decide))
    (e.injective.ne (by decide))
    (hmem 0) (hmem 1) (hmem 2)
  exact radius_gt_two_sqrt_three_of_F_sq b hb hFstrict

end CP15
