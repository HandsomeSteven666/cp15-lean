import CP15.M2K9DistinctStrongBudget
import CP15.M2K9DistinctCaseIAngles

open scoped InnerProductSpace

namespace CP15

set_option maxHeartbeats 0

/-- The extra A2-H1 contact alternative is excluded from the original
selected packing. The strictness of its other contact, the nonblocking
extra contact, the two-high outer budget, and all six directed gaps are
connected here; none of those geometric reductions is assumed numerically. -/
theorem SelectedPacking15.distinct_case_i_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hm2 : (nonOuterIndices p b).card = 2)
    (ix : Fin 6 → Fin 15) (hix : Function.Injective ix)
    (φ : Fin 6 → ℝ) (ε : ℝ) (hframe : LiftedSixFrame (fun i => p (ix i)) φ ε)
    (hinner : ∀ i, ‖p (ix i)‖ < b)
    (hA : ∀ i, wordAHAHLL i = .A →
      (699 / 1000 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 1301 / 1000)
    (hH : ∀ i, wordAHAHLL i = .H →
      (2 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, wordAHAHLL i = .L →
      (3 / 2 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 2)
    (h01 : dist (p (ix 0)) (p (ix 1)) = 2 ∧
      ‖p (ix 0)‖ ^ 2 < ⟪p (ix 1), p (ix 0)⟫_ℝ)
    (h23 : dist (p (ix 2)) (p (ix 3)) = 2 ∧
      ‖p (ix 2)‖ ^ 2 < ⟪p (ix 3), p (ix 2)⟫_ℝ)
    (h21 : dist (p (ix 2)) (p (ix 1)) = 2) : False := by
  have hfront := h.two_core_distinct hm2
  have hK9 := hfront.1
  have hbhalf := hfront.2.1
  have ha0 := hA 0 (by rfl)
  have ha2 := hA 2 (by rfl)
  have hh1 := hH 1 (by rfl)
  have hh3 := hH 3 (by rfl)
  have hl4 := hL 4 (by rfl)
  have hl5 := hL 5 (by rfl)
  have hno (i : Fin 6) (hi : wordAHAHLL i = .A) :
      ‖p (ix i)‖ < b ∧ ¬TouchesOuter p b (ix i) := by
    refine ⟨hinner i, ?_⟩
    intro ht
    have hlow := touching_radius_ge_three_halves p b (ix i) hbhalf ht
    linarith [(hA i hi).2]
  have hnonblock := h.common_contact_radius_nonblocking hm2 (ix 0) (ix 2) (ix 1)
    (hix.ne (by decide)) (hno 0 rfl) (hno 2 rfl) (hinner 1) h01.1 h21 h01.2
  have hsq1 : 4 + ‖p (ix 0)‖ ^ 2 < ‖p (ix 1)‖ ^ 2 := by
    linarith [blocker_radius_sq (p (ix 0)) (p (ix 1)) h01.1 h01.2]
  have hsq3 : 4 + ‖p (ix 2)‖ ^ 2 < ‖p (ix 3)‖ ^ 2 := by
    linarith [blocker_radius_sq (p (ix 2)) (p (ix 3)) h23.1 h23.2]
  have hcoreLt : ‖p (ix 0)‖ < ‖p (ix 2)‖ := by nlinarith [ha0.1, ha2.1]
  have hhighLt : ‖p (ix 1)‖ < ‖p (ix 3)‖ := by nlinarith [hh1.1, hh3.1]
  have hcoreSum : 2 ≤ ‖p (ix 0)‖ + ‖p (ix 2)‖ :=
    (h.separated (ix 0) (ix 2) (hix.ne (by decide : (0 : Fin 6) ≠ 2))).trans (by
      simpa [dist_eq_norm] using norm_sub_le (p (ix 0)) (p (ix 2)))
  have hcore2lo : 1 ≤ ‖p (ix 2)‖ := by linarith
  have hh1cap : ‖p (ix 1)‖ ≤ 23 / 10 := by
    rcases h.two_high_min_radius_lt_23_div_10 hK9 (by linarith) (ix 1) (ix 3)
      (hix.ne (by decide)) (hinner 1) (hinner 3) hh1.1 hh3.1 with hcap | hcap
    · exact hcap.le
    · exact (hhighLt.trans hcap).le
  have hsep6 : Separated (fun i => p (ix i)) 2 := fun i j hij =>
    h.separated _ _ (hix.ne hij)
  have hc5 : Real.cos (polarArg (p (ix 0)) - polarArg (p (ix 5))) =
      Real.cos (distinctSixGap φ 5) := by
    rw [show polarArg (p (ix 0)) - polarArg (p (ix 5)) =
      -(polarArg (p (ix 5)) - polarArg (p (ix 0))) by ring, Real.cos_neg]
    exact hframe.gap_cos 5
  have hc1 : Real.cos (polarArg (p (ix 2)) - polarArg (p (ix 1))) =
      Real.cos (distinctSixGap φ 1) := by
    rw [show polarArg (p (ix 2)) - polarArg (p (ix 1)) =
      -(polarArg (p (ix 1)) - polarArg (p (ix 2))) by ring, Real.cos_neg]
    exact hframe.gap_cos 1
  have hsum0 := distinct_case_i_AH_AL_sum_gt_131 (p (ix 0)) (p (ix 1)) (p (ix 5))
    (distinctSixGap φ 0) (distinctSixGap φ 5) ha0.1 ha0.2 hh1.1 hh1cap hl5.1 hl5.2
    (hsep6 0 1 (by decide)) (hsep6 0 5 (by decide))
    (hframe.gap_cos 0) hc5 (hframe.gap_nonneg 0) (hframe.gap_nonneg 5)
  have hsum2 := distinct_case_i_two_AH_sum_gt_115_8 (p (ix 2)) (p (ix 1)) (p (ix 3))
    (distinctSixGap φ 1) (distinctSixGap φ 2) hcore2lo ha2.2 hh1.1 hh1cap hh3.1
    (by linarith [hh3.2])
    (hsep6 2 1 (by decide)) (hsep6 2 3 (by decide))
    hc1 (hframe.gap_cos 2) (hframe.gap_nonneg 1) (hframe.gap_nonneg 2)
  have hHL : (533 / 10 : ℝ) * Real.pi / 180 < distinctSixGap φ 3 := by
    apply directed_pair_box_angle_gt (p (ix 3)) (p (ix 4)) (distinctSixGap φ 3)
      (533 / 10) (1195 / 2000) 2 (2385436 / 1000000) (3 / 2) 2
      (by norm_num) (by norm_num) hh3.1 hh3.2 hl4.1 hl4.2
      (hsep6 3 4 (by decide)) (hframe.gap_cos 3) (hframe.gap_nonneg 3)
      (by norm_num) (by norm_num)
    · apply cos_degrees_lower_of_certificate _ _ (by norm_num) (by norm_num)
      norm_num
    all_goals norm_num [pairExpr]
  have hLweak (i : Fin 6) (hi : wordAHAHLL i = .L) :
      (7 / 5 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 2 :=
    ⟨by linarith [(hL i hi).1], (hL i hi).2⟩
  have hLL := lifted_distinct_gap_cost (fun i => p (ix i)) hsep6 φ ε hframe
    wordAHAHLL hA hH hLweak 4
  norm_num [wordAHAHLL, classGapCost] at hLL
  have hcircle := distinctSixGap_sum φ
  rw [Fin.sum_univ_six] at hcircle
  nlinarith [Real.pi_pos]

/-- Only the A1-A2 contact alternative remains in the distinct branch.
The returned witnesses are still actual indices in the original packing. -/
theorem SelectedPacking15.actual_distinct_core_contact
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hm2 : (nonOuterIndices p b).card = 2) :
    ∃ ix : Fin 6 → Fin 15, ∃ φ : Fin 6 → ℝ, ∃ ε : ℝ,
      Function.Injective ix ∧ LiftedSixFrame (fun i => p (ix i)) φ ε ∧
      (∀ i, ‖p (ix i)‖ < b) ∧
      (∀ i, wordAHAHLL i = .A →
        (699 / 1000 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 1301 / 1000) ∧
      (∀ i, wordAHAHLL i = .H →
        (2 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 2385436 / 1000000) ∧
      (∀ i, wordAHAHLL i = .L →
        (3 / 2 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 2) ∧
      (dist (p (ix 0)) (p (ix 1)) = 2 ∧
        ‖p (ix 0)‖ ^ 2 < ⟪p (ix 1), p (ix 0)⟫_ℝ) ∧
      (dist (p (ix 2)) (p (ix 3)) = 2 ∧
        ‖p (ix 2)‖ ^ 2 < ⟪p (ix 3), p (ix 2)⟫_ℝ) ∧
      dist (p (ix 2)) (p (ix 0)) = 2 := by
  obtain ⟨ix, φ, ε, hix, _, hinner, _, hframe, _, hA, hH, hL, h01, h23, _, halt⟩ :=
    h.actual_distinct_contact_split hm2
  have hAA : dist (p (ix 2)) (p (ix 0)) = 2 := by
    rcases halt with hAA | h21
    · exact hAA
    · exact False.elim (h.distinct_case_i_impossible hm2 ix hix φ ε hframe
        hinner hA hH hL h01 h23 h21)
  exact ⟨ix, φ, ε, hix, hframe, hinner, hA, hH, hL, h01, h23, hAA⟩

end CP15
