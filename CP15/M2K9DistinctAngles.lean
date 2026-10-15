import CP15.M2K9PairCorners
import CP15.M2K9ClassWords

namespace CP15

noncomputable def distinctSixGap (φ : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
  if i = 5 then φ 0 + 2 * Real.pi - φ 5 else φ (i + 1) - φ i

theorem distinctSixGap_sum (φ : Fin 6 → ℝ) :
    (∑ i : Fin 6, distinctSixGap φ i) = 2 * Real.pi := by
  rw [Fin.sum_univ_six]
  simp [distinctSixGap]

private theorem distinctSixGap_nonneg (φ : Fin 6 → ℝ)
    (hmono : StrictMono φ)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (i : Fin 6) : 0 ≤ distinctSixGap φ i := by
  by_cases hi : i = 5
  · subst i
    simp [distinctSixGap]
    linarith
  · have hlt : i < i + 1 := by
      fin_cases i <;> simp_all
    have hφ := hmono hlt
    simp [distinctSixGap, hi]
    linarith

theorem distinctSixGap_cos_lift
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (i : Fin 6) :
    Real.cos (polarArg (q i) - polarArg (q (i + 1))) =
      Real.cos (distinctSixGap φ i) := by
  by_cases hi : i = 5
  · subst i
    simp [distinctSixGap, harg]
    have heq : φ 5 - φ 0 =
        2 * Real.pi - (φ 0 + 2 * Real.pi - φ 5) := by ring
    rw [heq, Real.cos_two_pi_sub]
  · rw [harg i, harg (i + 1)]
    simp only [distinctSixGap, hi, ↓reduceIte]
    rw [← Real.cos_neg (φ (i + 1) - φ i)]
    congr 1
    ring

theorem distinct_gap_cost
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
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
  have hg0 := distinctSixGap_nonneg φ hmono hfirst hlast i
  have hcos := distinctSixGap_cos_lift q φ harg i
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

/-- Every consecutive angular gap in the ordered six-center model is at
least 49 degrees. This follows from the exact radius-class contact bounds,
including the wrap-around gap. -/
theorem distinct_order_gap_at_least_49
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (w : Fin 6 → M2Kind)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L →
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (i : Fin 6) :
    49 * Real.pi / 180 ≤ distinctSixGap φ i := by
  have hcost := distinct_gap_cost q hsep φ hmono harg hfirst hlast
    w hA hH hL i
  have hweight : 490 ≤ classGapCost (w i) (w (i + 1)) := by
    cases w i <;> cases w (i + 1) <;> norm_num [classGapCost]
  have hweightR : (490 : ℝ) ≤
      (classGapCost (w i) (w (i + 1)) : ℕ) := by
    exact_mod_cast hweight
  have hmul := mul_le_mul_of_nonneg_right hweightR Real.pi_pos.le
  have hscaled : 49 * Real.pi / 180 ≤
      (classGapCost (w i) (w (i + 1)) : ℕ) * Real.pi / 1800 := by
    nlinarith
  exact hscaled.trans hcost

/-- The actual six ordered, separated centers pay the finite class budget.
The only inputs are their proven class radii and actual pairwise separation. -/
theorem distinct_order_class_budget
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (w : Fin 6 → M2Kind)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L →
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2) :
    classBudget w ≤ 3600 := by
  have hcost (i : Fin 6) :
      ((classGapCost (w i) (w (i + 1)) : ℕ) : ℝ) *
        Real.pi / 1800 ≤ distinctSixGap φ i :=
    distinct_gap_cost q hsep φ hmono harg hfirst hlast w hA hH hL i
  have hsumlt :
      (∑ i : Fin 6,
        ((classGapCost (w i) (w (i + 1)) : ℕ) : ℝ) * Real.pi / 1800) ≤
      ∑ i : Fin 6, distinctSixGap φ i :=
    Finset.sum_le_sum (fun i _ => hcost i)
  rw [distinctSixGap_sum] at hsumlt
  have hbudgetCast :
      ((classBudget w : ℕ) : ℝ) =
        ∑ i : Fin 6, ((classGapCost (w i) (w (i + 1)) : ℕ) : ℝ) := by
    simp [classBudget]
  have hfactored :
      ((∑ i : Fin 6,
        ((classGapCost (w i) (w (i + 1)) : ℕ) : ℝ)) * Real.pi / 1800) ≤
      2 * Real.pi := by
    calc
      (∑ i : Fin 6,
          ((classGapCost (w i) (w (i + 1)) : ℕ) : ℝ)) * Real.pi / 1800 =
          ∑ i : Fin 6,
            ((classGapCost (w i) (w (i + 1)) : ℕ) : ℝ) * Real.pi / 1800 := by
              rw [← Finset.sum_div, ← Finset.sum_mul]
      _ ≤ 2 * Real.pi := hsumlt
  rw [← hbudgetCast] at hfactored
  have hcast : ((classBudget w : ℕ) : ℝ) ≤ 3600 := by
    nlinarith [Real.pi_pos]
  exact_mod_cast hcast

end CP15
