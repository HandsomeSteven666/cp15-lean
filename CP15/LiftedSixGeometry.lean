import CP15.CyclicSixFrame

namespace CP15

theorem LiftedSixFrame.gap_nonneg {q : Fin 6 → Plane} {φ : Fin 6 → ℝ}
    {ε : ℝ} (h : LiftedSixFrame q φ ε) (i : Fin 6) :
    0 ≤ distinctSixGap φ i := by
  by_cases hi : i = 5
  · subst i
    simp [distinctSixGap]
    linarith [h.span]
  · have hlt : i < i + 1 := by fin_cases i <;> simp_all
    have hm := h.mono hlt
    simp [distinctSixGap, hi]
    linarith

theorem LiftedSixFrame.gap_cos {q : Fin 6 → Plane} {φ : Fin 6 → ℝ}
    {ε : ℝ} (h : LiftedSixFrame q φ ε) (i : Fin 6) :
    Real.cos (polarArg (q i) - polarArg (q (i + 1))) =
      Real.cos (distinctSixGap φ i) := by
  rw [h.cosine]
  by_cases hi : i = 5
  · subst i
    simp [distinctSixGap]
    have heq : φ 5 - φ 0 = 2 * Real.pi - (φ 0 + 2 * Real.pi - φ 5) := by ring
    rw [heq, Real.cos_two_pi_sub]
  · simp only [distinctSixGap, hi, ↓reduceIte]
    rw [← Real.cos_neg (φ (i + 1) - φ i)]
    congr 1
    ring

theorem LiftedSixFrame.arc_range {q : Fin 6 → Plane} {φ : Fin 6 → ℝ}
    {ε : ℝ} (h : LiftedSixFrame q φ ε) (a b : Fin 6) :
    0 ≤ distinctForwardArc φ a b ∧ distinctForwardArc φ a b ≤ 2 * Real.pi := by
  have ha0 : φ 0 ≤ φ a := h.mono.monotone (by omega)
  have hb0 : φ 0 ≤ φ b := h.mono.monotone (by omega)
  have ha5 : φ a ≤ φ 5 := h.mono.monotone (by omega)
  have hb5 : φ b ≤ φ 5 := h.mono.monotone (by omega)
  have hs := h.span
  by_cases hab : a.val < b.val
  · have hm := h.mono (show a < b from hab)
    simp only [distinctForwardArc, if_pos hab]
    constructor <;> linarith
  · have hm := h.mono.monotone (show b ≤ a by omega)
    simp only [distinctForwardArc, if_neg hab]
    constructor <;> linarith

theorem lifted_forward_arc_sin (φ : Fin 6 → ℝ) (a b : Fin 6) :
    Real.sin (φ b - φ a) = Real.sin (distinctForwardArc φ a b) := by
  by_cases hab : a.val < b.val
  · simp [distinctForwardArc, hab]
  · have heq : distinctForwardArc φ a b = (φ b - φ a) + 2 * Real.pi := by
      simp [distinctForwardArc, hab]
      ring
    rw [heq, Real.sin_add_two_pi]

theorem LiftedSixFrame.arc_cos {q : Fin 6 → Plane} {φ : Fin 6 → ℝ}
    {ε : ℝ} (h : LiftedSixFrame q φ ε) (a b : Fin 6) :
    Real.cos (polarArg (q a) - polarArg (q b)) =
      Real.cos (distinctForwardArc φ a b) := by
  rw [h.cosine]
  by_cases hab : a.val < b.val
  · simp only [distinctForwardArc, if_pos hab]
    rw [← Real.cos_neg (φ b - φ a)]
    congr 1
    ring
  · have heq : distinctForwardArc φ a b = (φ b - φ a) + 2 * Real.pi := by
      simp [distinctForwardArc, hab]
      ring
    rw [heq, Real.cos_add_two_pi]
    rw [← Real.cos_neg (φ b - φ a)]
    congr 1
    ring

theorem LiftedSixFrame.negative_cross_backward_arc_lt_pi
    {q : Fin 6 → Plane} {φ : Fin 6 → ℝ} {ε : ℝ}
    (h : LiftedSixFrame q φ ε) (a j : Fin 6) (haj : a ≠ j)
    (ha : 0 < ‖q a‖) (hj : 0 < ‖q j‖)
    (hcross : ε * planeCross (q a) (q j - q a) < 0) :
    distinctForwardArc φ j a < Real.pi := by
  have hexpand : planeCross (q a) (q j - q a) = planeCross (q a) (q j) := by
    simp [planeCross]
    ring
  rw [hexpand, h.cross, lifted_forward_arc_sin] at hcross
  have hp := mul_pos ha hj
  have hsin : Real.sin (distinctForwardArc φ a j) < 0 := by nlinarith
  have hr := h.arc_range a j
  have hforward : Real.pi < distinctForwardArc φ a j := by
    by_contra hn
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hr.1 (le_of_not_gt hn)
    linarith
  have hcomp := distinctForwardArc_complement φ a j haj
  linarith

theorem lifted_distinct_gap_cost
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (ε : ℝ) (hframe : LiftedSixFrame q φ ε)
    (w : Fin 6 → M2Kind)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L →
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (i : Fin 6) :
    ((classGapCost (w i) (w (i + 1)) : ℕ) : ℝ) *
      Real.pi / 1800 ≤ distinctSixGap φ i := by
  let j := i + 1
  have hij : i ≠ j := by dsimp [j]; fin_cases i <;> decide
  have hsepij : 2 ≤ dist (q i) (q j) := hsep i j hij
  have hg0 := hframe.gap_nonneg i
  have hcos := hframe.gap_cos i
  have hcosrev :
      Real.cos (polarArg (q j) - polarArg (q i)) =
        Real.cos (distinctSixGap φ i) := by
    have heq : polarArg (q j) - polarArg (q i) =
        -(polarArg (q i) - polarArg (q j)) := by ring
    rw [heq, Real.cos_neg]
    exact hcos
  by_cases hgpi : distinctSixGap φ i ≤ Real.pi
  · cases hwi : w i <;> cases hwj : w j
    · have hi := hA i hwi
      have hj := hA j hwj
      have ha := distinct_AA_angle_gt_100 (q i) (q j)
        (distinctSixGap φ i) hi.1 hi.2 hj.1 hj.2 hsepij hcos hg0 hgpi
      simp [classGapCost, hwi, hwj, j]
      nlinarith [Real.pi_pos]
    · have hi := hA i hwi
      have hj := hH j hwj
      have ha := shared_AH_angle_gt_49_2 (q i) (q j)
        (distinctSixGap φ i) hi.1 hi.2 hj.1 hj.2 hsepij hcos hg0 hgpi
      simp [classGapCost, hwi, hwj, j]
      linarith [Real.pi_pos]
    · have hi := hA i hwi
      have hj := hL j hwj
      have ha := shared_AL_angle_gt_70_8 (q i) (q j)
        (distinctSixGap φ i) hi.1 hi.2 hj.1 hj.2 hsepij hcos hg0 hgpi
      simp [classGapCost, hwi, hwj, j]
      linarith [Real.pi_pos]
    · have hi := hH i hwi
      have hj := hA j hwj
      have ha := shared_AH_angle_gt_49_2 (q j) (q i)
        (distinctSixGap φ i) hj.1 hj.2 hi.1 hi.2
        (by simpa [dist_comm] using hsepij) hcosrev hg0 hgpi
      simp [classGapCost, hwi, hwj, j]
      linarith [Real.pi_pos]
    · have hi := hH i hwi
      have hj := hH j hwj
      have ha := distinct_HH_angle_gt_49_2 (q i) (q j)
        (distinctSixGap φ i) hi.1 hi.2 hj.1 hj.2 hsepij hcos hg0 hgpi
      simp [classGapCost, hwi, hwj, j]
      linarith [Real.pi_pos]
    · have hi := hH i hwi
      have hj := hL j hwj
      have ha := shared_HL_angle_gt_53 (q i) (q j)
        (distinctSixGap φ i) hi.1 hi.2 hj.1 hj.2 hsepij hcos hg0 hgpi
      simp [classGapCost, hwi, hwj, j]
      linarith [Real.pi_pos]
    · have hi := hL i hwi
      have hj := hA j hwj
      have ha := shared_AL_angle_gt_70_8 (q j) (q i)
        (distinctSixGap φ i) hj.1 hj.2 hi.1 hi.2
        (by simpa [dist_comm] using hsepij) hcosrev hg0 hgpi
      simp [classGapCost, hwi, hwj, j]
      linarith [Real.pi_pos]
    · have hi := hL i hwi
      have hj := hH j hwj
      have ha := shared_HL_angle_gt_53 (q j) (q i)
        (distinctSixGap φ i) hj.1 hj.2 hi.1 hi.2
        (by simpa [dist_comm] using hsepij) hcosrev hg0 hgpi
      simp [classGapCost, hwi, hwj, j]
      linarith [Real.pi_pos]
    · have hi := hL i hwi
      have hj := hL j hwj
      have ha := shared_LL_angle_ge_60 (q i) (q j)
        (distinctSixGap φ i) hi.1 hi.2 hj.1 hj.2 hsepij hcos hg0 hgpi
      simp [classGapCost, hwi, hwj, j]
      linarith [Real.pi_pos]
  · have hglarge : Real.pi < distinctSixGap φ i := lt_of_not_ge hgpi
    have hweight : classGapCost (w i) (w j) ≤ 1000 := by
      cases w i <;> cases w j <;> norm_num [classGapCost]
    have hweightR :
        ((classGapCost (w i) (w j) : ℕ) : ℝ) ≤ 1000 :=
      Nat.cast_le.mpr hweight
    have hπpos : 0 < Real.pi := Real.pi_pos
    have hcost :
        ((classGapCost (w i) (w j) : ℕ) : ℝ) * Real.pi / 1800 < Real.pi := by
      nlinarith
    exact hcost.le.trans hglarge.le


end CP15
