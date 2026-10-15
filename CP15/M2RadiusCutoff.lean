import CP15.NonOuterStructure

open scoped InnerProductSpace

namespace CP15

/-- The algebraic radius consequence of the strict two-point cap. -/
theorem radius_gt_sqrt5_sqrt21_half_of_F_gt_one (b : ℝ) (hb : 2 < b)
    (hF : 1 < F b) :
    (Real.sqrt 5 + Real.sqrt 21) / 2 < b := by
  have hs5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs21 : (Real.sqrt 21) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hs5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs21pos : 0 < Real.sqrt 21 := Real.sqrt_pos.2 (by norm_num)
  have hDpos : 0 < D b := D_pos hb
  have hrad : 0 ≤ D b ^ 2 - 4 := by
    by_contra hnot
    have hzero : F b = 0 := by
      unfold F
      exact Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hnot)
    linarith
  have hFsq : F b ^ 2 = D b ^ 2 - 4 := by
    unfold F
    exact Real.sq_sqrt hrad
  have hDsq : 5 < D b ^ 2 := by nlinarith
  let q : ℝ := (Real.sqrt 5 + Real.sqrt 21) / 2
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqpoly : q ^ 2 - Real.sqrt 5 * q - 4 = 0 := by
    dsimp [q]
    nlinarith
  have hDq : D q = Real.sqrt 5 := by
    dsimp [D]
    field_simp
    nlinarith [hqpoly]
  by_contra hnot
  have hbq : b ≤ q := le_of_not_gt hnot
  have hrec : 4 / q ≤ 4 / b := by
    apply (div_le_div_iff₀ hqpos (by linarith)).2
    nlinarith
  have hDle : D b ≤ D q := by
    unfold D
    linarith
  rw [hDq] at hDle
  nlinarith

/-- Two non-outer centers in a selected packing force the strict
`m = 2` radius cutoff, with no chosen-label assumption. -/
theorem m2_radius_cutoff (p : Fin 15 → Plane) (b : ℝ) (hb : 2 < b)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ q, ‖p q‖ < b → ‖p q‖ < D b)
    (hblock : ∀ q, ‖p q‖ < b → p q ≠ 0 →
      ∃ j, j ≠ q ∧ dist (p q) (p j) = 2 ∧
        ‖p q‖ ^ 2 < ⟪p j, p q⟫_ℝ)
    (hFcap : ∀ q, ‖p q‖ < b → ¬TouchesOuter p b q → ‖p q‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hm2 : 2 ≤ (nonOuterIndices p b).card) :
    (Real.sqrt 5 + Real.sqrt 21) / 2 < b := by
  classical
  have htwo : Fintype.card (Fin 2) ≤ (nonOuterIndices p b).card := by
    simpa using hm2
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset htwo
  have hmem (a : Fin 2) :
      ‖p (e a)‖ < b ∧ ¬TouchesOuter p b (e a) := by
    have ha : e a ∈ nonOuterIndices p b := he ⟨a, rfl⟩
    simpa [nonOuterIndices] using ha
  have hFstrict := two_nonOuter_F_gt_one p b hb hpack hD hblock
    hFcap hFsmall (e 0) (e 1) (e.injective.ne (by decide))
    (hmem 0) (hmem 1)
  exact radius_gt_sqrt5_sqrt21_half_of_F_gt_one b hb hFstrict

end CP15
