import CP15.M2K9DistinctCaseIClosed
import CP15.M2K9DistinctCaseIICertificate

open scoped InnerProductSpace

namespace CP15

set_option maxHeartbeats 0

/-- The remaining distinct-blocker case is excluded using a complete
closed rational cover. All radii, support offsets and directed arcs in
the certificate are supplied by actual centers of the selected packing. -/
theorem SelectedPacking15.two_core_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hm2 : (nonOuterIndices p b).card = 2) : False := by
  obtain ⟨ix, φ, ε, hix, hframe, hinner, hA, hH, hL, h01, h23, _⟩ :=
    h.actual_distinct_core_contact hm2
  have hfront := h.two_core_distinct hm2
  have hb : 3 < b := by linarith [hfront.2.1]
  have ha0 := hA 0 (by rfl)
  have ha2 := hA 2 (by rfl)
  have hh1 := hH 1 (by rfl)
  have hh3 := hH 3 (by rfl)
  have hl4 := hL 4 (by rfl)
  have hl5 := hL 5 (by rfl)
  have hsq1 : 4 + ‖p (ix 0)‖ ^ 2 < ‖p (ix 1)‖ ^ 2 := by
    linarith [blocker_radius_sq (p (ix 0)) (p (ix 1)) h01.1 h01.2]
  have hsq3 : 4 + ‖p (ix 2)‖ ^ 2 < ‖p (ix 3)‖ ^ 2 := by
    linarith [blocker_radius_sq (p (ix 2)) (p (ix 3)) h23.1 h23.2]
  obtain ⟨δ, hδ, hbudget, hlaw1, hlaw3, _, _⟩ :=
    h.two_high_strong_budget hfront.1 (ix 1) (ix 3)
      (hix.ne (by decide)) (hinner 1) (hinner 3) hh1.1 hh3.1
  have hsep6 : Separated (fun i => p (ix i)) 2 := fun i j hij =>
    h.separated _ _ (hix.ne hij)
  have hc5 : Real.cos (polarArg (p (ix 0)) - polarArg (p (ix 5))) =
      Real.cos (distinctSixGap φ 5) := by
    rw [show polarArg (p (ix 0)) - polarArg (p (ix 5)) =
      -(polarArg (p (ix 5)) - polarArg (p (ix 0))) by ring, Real.cos_neg]
    exact hframe.gap_cos 5
  have hLweak (i : Fin 6) (hi : wordAHAHLL i = .L) :
      (7 / 5 : ℝ) ≤ ‖p (ix i)‖ ∧ ‖p (ix i)‖ ≤ 2 :=
    ⟨by linarith [(hL i hi).1], (hL i hi).2⟩
  have hLL := lifted_distinct_gap_cost (fun i => p (ix i)) hsep6 φ ε hframe
    wordAHAHLL hA hH hLweak 4
  norm_num [wordAHAHLL, classGapCost] at hLL
  have hcircle := distinctSixGap_sum φ
  rw [Fin.sum_univ_six] at hcircle
  have harc : distinctForwardArc φ 0 2 =
      distinctSixGap φ 0 + distinctSixGap φ 1 := by
    norm_num [distinctForwardArc, distinctSixGap]
  have hangle : distinctForwardArc φ 0 2 + distinctSixGap φ 2 +
      distinctSixGap φ 3 + distinctSixGap φ 5 ≤ 300 * Real.pi / 180 := by
    rw [harc]
    linarith
  exact distinct_case_ii_scalar_cover (p (ix 0)) (p (ix 2))
    (p (ix 1)) (p (ix 3)) (p (ix 4)) (p (ix 5)) b (δ 0) (δ 1)
    (distinctForwardArc φ 0 2) (distinctSixGap φ 2)
    (distinctSixGap φ 3) (distinctSixGap φ 5) hb
    (h.belowCandidate.trans Candidate.candidateB_lt_352136_div_100000.le)
    ha0.1 ha0.2 ha2.1 ha2.2 hh1.1 hh1.2 hh3.1 hh3.2
    hl4.1 hl4.2 hl5.1 hl5.2 hsq1 hsq3
    (hδ 0).1 (hδ 0).2 (hδ 1).1 (hδ 1).2 hlaw1 hlaw3 hbudget
    (hsep6 0 2 (by decide)) (hsep6 2 3 (by decide))
    (hsep6 3 4 (by decide)) (hsep6 0 5 (by decide))
    (hframe.arc_cos 0 2) (hframe.gap_cos 2) (hframe.gap_cos 3) hc5
    (hframe.arc_range 0 2).1 (hframe.gap_nonneg 2)
    (hframe.gap_nonneg 3) (hframe.gap_nonneg 5) hangle

/-- The original optimization problem admits a selected optimal
representative with at most one non-outer-contacting center. -/
theorem SelectedPacking15.core_count_le_one
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b) :
    (nonOuterIndices p b).card ≤ 1 := by
  by_contra hn
  have hm2 : (nonOuterIndices p b).card = 2 := by
    have := h.coreCount
    omega
  exact h.two_core_impossible hm2

theorem exists_selectedPacking15_at_seven_rows :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane, SelectedPacking15 p b ∧
      SevenResidualRows (boundarySet p b).card (nonOuterIndices p b).card := by
  obtain ⟨b, p, h⟩ := exists_selectedPacking15
  exact ⟨b, p, h, h.seven_rows h.core_count_le_one⟩

end CP15
