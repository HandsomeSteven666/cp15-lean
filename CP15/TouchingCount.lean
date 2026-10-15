import CP15.ElementaryRadius
import CP15.PolarOrder

open scoped InnerProductSpace

namespace CP15

private noncomputable def touchingEightGap (φ : Fin 8 → ℝ) (i : Fin 8) : ℝ :=
  if i = 7 then φ 0 + 2 * Real.pi - φ 7 else φ (i + 1) - φ i

private theorem touchingEightGap_sum (φ : Fin 8 → ℝ) :
    (∑ i : Fin 8, touchingEightGap φ i) = 2 * Real.pi := by
  rw [Fin.sum_univ_eight]
  simp [touchingEightGap]

private theorem touchingEightGap_cos_lift
    (q : Fin 8 → Plane) (φ : Fin 8 → ℝ)
    (harg : ∀ i, polarArg (q i) = φ i) (i : Fin 8) :
    Real.cos (polarArg (q i) - polarArg (q (i + 1))) =
      Real.cos (touchingEightGap φ i) := by
  by_cases hi : i = 7
  · subst i
    simp [touchingEightGap, harg]
    have heq : φ 7 - φ 0 = 2 * Real.pi -
        (φ 0 + 2 * Real.pi - φ 7) := by ring
    rw [heq, Real.cos_two_pi_sub]
  · rw [harg i, harg (i + 1)]
    simp only [touchingEightGap, hi, ↓reduceIte]
    rw [← Real.cos_neg (φ (i + 1) - φ i)]
    congr 1
    ring

/-- A uniform annular angle bound, including unequal radii and any
nonnegative lift of the angular gap. The four corners are exact rationals. -/
theorem touching_annulus_pair_angle_gt_four_fifths
    (x y : Plane) (g : ℝ)
    (hxlo : (4 / 5 : ℝ) ≤ ‖x‖) (hxhi : ‖x‖ ≤ 12 / 5)
    (hylo : (4 / 5 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ 12 / 5)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) : (4 / 5 : ℝ) < g := by
  have hbox := pairExpr_lt_four_of_corners (4 / 5) ‖x‖ (12 / 5)
    (4 / 5) ‖y‖ (12 / 5) (17 / 25)
    hxlo hxhi hylo hyhi (by norm_num [pairExpr]) (by norm_num [pairExpr])
    (by norm_num [pairExpr]) (by norm_num [pairExpr])
  have hdist : 4 ≤ dist x y ^ 2 := by
    nlinarith [dist_nonneg (x := x) (y := y)]
  rw [dist_eq_norm, norm_sub_sq_real, polar_inner, hcos] at hdist
  by_contra hnot
  have hg : g ≤ 4 / 5 := le_of_not_gt hnot
  have hsquare : g ^ 2 ≤ (4 / 5 : ℝ) ^ 2 := by nlinarith
  have hc : (17 / 25 : ℝ) ≤ Real.cos g := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := g)]
  have hprod : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcmul := mul_le_mul_of_nonneg_left hc hprod
  dsimp [pairExpr] at hbox
  nlinarith

/-- Eight separated points in the touching-center annulus are impossible.
The sort is an actual permutation and the eighth gap is the wrap gap. -/
theorem eight_touching_annulus_impossible (q : Fin 8 → Plane)
    (hsep : Separated q 2)
    (hlo : ∀ i, (4 / 5 : ℝ) ≤ ‖q i‖)
    (hhi : ∀ i, ‖q i‖ ≤ 12 / 5) : False := by
  have hpolar : Function.Injective (fun i => polarArg (q i)) := by
    intro i j harg
    by_contra hij
    have hd := hsep i j hij
    have hdsq : 4 ≤ dist (q i) (q j) ^ 2 := by
      nlinarith [dist_nonneg (x := q i) (y := q j)]
    rw [dist_eq_norm, norm_sub_sq_real, polar_inner] at hdsq
    change polarArg (q i) = polarArg (q j) at harg
    rw [harg, sub_self, Real.cos_zero] at hdsq
    have hi0 := hlo i
    have hj0 := hlo j
    have hi1 := hhi i
    have hj1 := hhi j
    nlinarith
  obtain ⟨src, φ, hsrc, hmono, harg, hrange⟩ :=
    exists_sorted_polar_permutation q hpolar
  let sorted : Fin 8 → Plane := fun i => q (src i)
  have hg (i : Fin 8) : (4 / 5 : ℝ) < touchingEightGap φ i := by
    have hg0 : 0 ≤ touchingEightGap φ i := by
      by_cases hi7 : i = 7
      · subst i
        simp [touchingEightGap]
        linarith [(hrange 0).1, (hrange 7).2]
      · have hlt : i < i + 1 := by fin_cases i <;> simp_all
        have hm := hmono hlt
        simp only [touchingEightGap, hi7, ↓reduceIte]
        linarith
    exact touching_annulus_pair_angle_gt_four_fifths (sorted i)
      (sorted (i + 1)) (touchingEightGap φ i)
      (hlo (src i)) (hhi (src i)) (hlo (src (i + 1))) (hhi (src (i + 1)))
      (hsep (src i) (src (i + 1)) (hsrc.1.ne (by fin_cases i <;> decide)))
      (touchingEightGap_cos_lift sorted φ harg i) hg0
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hg i).le)
  rw [touchingEightGap_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith [Real.pi_lt_d6]

/-- For every selected feasible packing at or below the candidate radius,
at most seven strictly inner centers touch the outer ring. -/
theorem touchingInner_count_le_seven (p : Fin 15 → Plane) (b : ℝ)
    (hbB : b ≤ candidateB) (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b) :
    (touchingInnerSet p b).card ≤ 7 := by
  classical
  have hfeas : CenterFeasible 15 b := ⟨p, hpack⟩
  have hbC := centerFeasible_radius_ge_one_add_sqrt_five hfeas
  have hbpos : 0 < b := by nlinarith [Real.sqrt_nonneg 5]
  have hbLow : (14 / 5 : ℝ) < b := by
    have h5sq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    nlinarith [Real.sqrt_nonneg 5]
  have hDhi := D_lt_twelve_fifths_of_le_candidateB b hbpos hbB
  by_contra hnot
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin 8) ≤ (touchingInnerSet p b).card by simp; omega)
  have hedata (i : Fin 8) : ‖p (e i)‖ < b ∧ TouchesOuter p b (e i) := by
    have hi := he ⟨i, rfl⟩
    simpa [touchingInnerSet] using hi
  have hlo (i : Fin 8) : (4 / 5 : ℝ) ≤ ‖p (e i)‖ := by
    obtain ⟨j, _, hj, hc⟩ := (hedata i).2
    have ht := norm_add_le (p j - p (e i)) (p (e i))
    rw [sub_add_cancel, hj] at ht
    have hd : ‖p j - p (e i)‖ = 2 := by
      simpa [dist_eq_norm, norm_sub_rev] using hc
    rw [hd] at ht
    linarith
  exact eight_touching_annulus_impossible (fun i => p (e i))
    (fun i j hij => hpack.2 (e i) (e j) (e.injective.ne hij)) hlo
    (fun i => ((hD (e i) (hedata i).1).trans hDhi).le)

end CP15
