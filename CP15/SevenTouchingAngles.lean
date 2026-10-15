import CP15.CyclicAngles
import CP15.RationalPairAngle

namespace CP15

set_option maxHeartbeats 0

theorem pairExpr_le_four_of_corners (a r b d s e c : ℝ)
    (har : a ≤ r) (hrb : r ≤ b) (hds : d ≤ s) (hse : s ≤ e)
    (had : pairExpr a d c ≤ 4) (hae : pairExpr a e c ≤ 4)
    (hbd : pairExpr b d c ≤ 4) (hbe : pairExpr b e c ≤ 4) :
    pairExpr r s c ≤ 4 := by
  have hcomm (x y : ℝ) : pairExpr x y c = pairExpr y x c := by
    unfold pairExpr
    ring
  have hs := pairExpr_le_endpoint_max d s e r c hds hse
  rw [hcomm s r, hcomm d r, hcomm e r] at hs
  exact hs.trans (max_le
    ((pairExpr_le_endpoint_max a r b d c har hrb).trans (max_le had hbd))
    ((pairExpr_le_endpoint_max a r b e c har hrb).trans (max_le hae hbe)))

/-- The sixty-degree bound holds on the full low touching annulus;
no radius lower bound from the two-core branch is imported. -/
theorem touching_low_pair_angle_ge_pi_div_three (x y : Plane) (g : ℝ)
    (hxlo : (6 / 5 : ℝ) ≤ ‖x‖) (hxhi : ‖x‖ ≤ 2)
    (hylo : (6 / 5 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ 2)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg : 0 ≤ g) : Real.pi / 3 ≤ g := by
  by_cases hgpi : g ≤ Real.pi
  · have hp := pairExpr_le_four_of_corners (6 / 5) ‖x‖ 2 (6 / 5) ‖y‖ 2 (1 / 2)
      hxlo hxhi hylo hyhi (by norm_num [pairExpr]) (by norm_num [pairExpr])
      (by norm_num [pairExpr]) (by norm_num [pairExpr])
    have hd : (4 : ℝ) ≤ dist x y ^ 2 := by
      nlinarith [dist_nonneg (x := x) (y := y)]
    rw [dist_eq_norm, norm_sub_sq_real, polar_inner, hcos] at hd
    have hc : Real.cos g ≤ 1 / 2 := by
      dsimp [pairExpr] at hp
      nlinarith [mul_pos (by linarith : 0 < ‖x‖) (by linarith : 0 < ‖y‖)]
    by_contra hn
    have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi hg
      (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) (lt_of_not_ge hn)
    rw [Real.cos_pi_div_three] at hlt
    linarith
  · linarith [Real.pi_pos]

def sevenTouchingDegrees (color : Fin 7 → Bool) (i : Fin 7) : ℚ :=
  if color i then if color (i + 1) then 60 else 213 / 4
  else if color (i + 1) then 213 / 4 else 246 / 5

/-- All 128 class words are checked, including every cyclic wrap pair.
Two or more low centers already require more than a full turn. -/
theorem sevenTouchingDegrees_gt_turn :
    ∀ color : Fin 7 → Bool,
      2 ≤ (Finset.univ.filter (fun i => color i)).card →
        (360 : ℚ) < ∑ i, sevenTouchingDegrees color i := by
  decide +kernel

/-- The actual seven-center annulus contains at most one center of norm
at most two. The sort is an actual permutation, not an assumed class word. -/
theorem seven_touching_at_most_one_low (q : Fin 7 → Plane)
    (hsep : Separated q 2)
    (hlo : ∀ i, (6 / 5 : ℝ) ≤ ‖q i‖)
    (hhi : ∀ i, ‖q i‖ ≤ 2385436 / 1000000) :
    (Finset.univ.filter (fun i => ‖q i‖ ≤ 2)).card ≤ 1 := by
  classical
  have hpolar := seven_polarArg_injective q hsep
    (fun i => by linarith [hlo i]) (fun i => by linarith [hhi i])
  obtain ⟨src, φ, hsrc, hmono, harg, hrange⟩ := exists_sorted_polar_permutation q hpolar
  let sorted : Fin 7 → Plane := fun i => q (src i)
  let color : Fin 7 → Bool := fun i => decide (‖sorted i‖ ≤ 2)
  have hgap (i : Fin 7) :
      (sevenTouchingDegrees color i : ℝ) * Real.pi / 180 ≤ cyclicAngleGap φ i := by
    let j := i + 1
    have hij : i ≠ j := by dsimp [j]; fin_cases i <;> decide
    have hsepij := hsep (src i) (src j) (hsrc.1.ne hij)
    have hc := cyclicAngleGap_cos sorted φ harg i
    have hg := cyclicAngleGap_nonneg φ hmono hrange i
    by_cases hi : ‖sorted i‖ ≤ 2 <;> by_cases hj : ‖sorted j‖ ≤ 2
    · have ht := touching_low_pair_angle_ge_pi_div_three (sorted i) (sorted j)
        (cyclicAngleGap φ i) (hlo (src i)) hi (hlo (src j)) hj hsepij hc hg
      simp [sevenTouchingDegrees, color, hi, hj, j]
      linarith
    · have ht : (213 / 4 : ℝ) * Real.pi / 180 < cyclicAngleGap φ i := by
        apply directed_pair_box_angle_gt (sorted i) (sorted j) (cyclicAngleGap φ i)
          (213 / 4) (597 / 1000) (6 / 5) 2 2 (2385436 / 1000000)
          (by norm_num) (by norm_num) (hlo (src i)) hi (by linarith) (hhi (src j))
          hsepij hc hg (by norm_num) (by norm_num)
        · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          norm_num
        all_goals norm_num [pairExpr]
      simp [sevenTouchingDegrees, color, hi, hj, j]
      exact ht.le
    · have hcr : Real.cos (polarArg (sorted j) - polarArg (sorted i)) =
          Real.cos (cyclicAngleGap φ i) := by
        rw [show polarArg (sorted j) - polarArg (sorted i) =
          -(polarArg (sorted i) - polarArg (sorted j)) by ring, Real.cos_neg]
        exact hc
      have ht : (213 / 4 : ℝ) * Real.pi / 180 < cyclicAngleGap φ i := by
        apply directed_pair_box_angle_gt (sorted j) (sorted i) (cyclicAngleGap φ i)
          (213 / 4) (597 / 1000) (6 / 5) 2 2 (2385436 / 1000000)
          (by norm_num) (by norm_num) (hlo (src j)) hj (by linarith) (hhi (src i))
          (by simpa [dist_comm] using hsepij) hcr hg (by norm_num) (by norm_num)
        · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
          norm_num
        all_goals norm_num [pairExpr]
      simp [sevenTouchingDegrees, color, hi, hj, j]
      exact ht.le
    · have ht := distinct_HH_angle_gt_49_2 (sorted i) (sorted j) (cyclicAngleGap φ i)
        (by linarith) (hhi (src i)) (by linarith) (hhi (src j)) hsepij hc hg
      by_cases hgpi : cyclicAngleGap φ i ≤ Real.pi
      · have ht' := ht hgpi
        simp [sevenTouchingDegrees, color, hi, hj, j]
        nlinarith [Real.pi_pos]
      · simp [sevenTouchingDegrees, color, hi, hj, j]
        nlinarith [Real.pi_pos]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hgap i)
  rw [cyclicAngleGap_sum] at hsum
  rw [← Finset.sum_div, ← Finset.sum_mul] at hsum
  have hcolorcard : (Finset.univ.filter (fun i => color i)).card =
      (Finset.univ.filter (fun i => ‖q i‖ ≤ 2)).card := by
    have hbij := Finset.card_image_of_injective
      (Finset.univ.filter (fun i => color i)) hsrc.1
    have heq : (Finset.univ.filter (fun i => color i)).image src =
        Finset.univ.filter (fun i => ‖q i‖ ≤ 2) := by
      ext i
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        simpa [color, sorted] using hj
      · intro hi
        obtain ⟨j, rfl⟩ := hsrc.2 i
        exact ⟨j, by simpa [color, sorted] using hi, rfl⟩
    rw [heq] at hbij
    exact hbij.symm
  by_contra hn
  have hcount : 2 ≤ (Finset.univ.filter (fun i => color i)).card := by
    rw [hcolorcard]
    omega
  have hdegrees : (360 : ℝ) < ∑ i, (sevenTouchingDegrees color i : ℝ) := by
    exact_mod_cast sevenTouchingDegrees_gt_turn color hcount
  nlinarith [Real.pi_pos]

end CP15
