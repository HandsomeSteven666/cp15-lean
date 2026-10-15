import CP15.M2K9DistinctCorePairs

namespace CP15

set_option maxHeartbeats 0 in

/-- The two-core H/L-flanking pattern is impossible. The proof uses the
actual ordered centers: each of the two cores contributes a paired gap
bound, while every remaining gap keeps its class-specific lower bound. The
six-word case split is kernel exhaustive. No convexity is assumed. -/
theorem distinct_both_core_high_low_impossible
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (w : Fin 6 → M2Kind)
    (hAcount : classCount w .A = 2)
    (hHcount : classCount w .H = 2)
    (hLcount : classCount w .L = 2)
    (hArad : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hHrad : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hLrad : ∀ i, w i = .L →
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (hflank : bothCoreHighLow w) : False := by
  have hpair (a : Fin 6) (ha : w a = .A) :
      127 * Real.pi / 180 <
        distinctSixGap φ (a - 1) + distinctSixGap φ a :=
    distinct_core_flanking_gap_sum_gt_127 q hsep φ hmono harg
      hfirst hlast w hArad hHrad hLrad a ha (hflank a ha)
  have hcost (i : Fin 6) :
      (classGapCost (w i) (w (i + 1)) : ℕ) * Real.pi / 1800 ≤
        distinctSixGap φ i :=
    distinct_gap_cost q hsep φ hmono harg hfirst hlast w
      hArad hHrad hLrad i
  have hsum := distinctSixGap_sum φ
  rw [Fin.sum_univ_six] at hsum
  have hm0 : (0 : Fin 6) - 1 = 5 := by decide
  have hm1 : (1 : Fin 6) - 1 = 0 := by decide
  have hm2 : (2 : Fin 6) - 1 = 1 := by decide
  have hm3 : (3 : Fin 6) - 1 = 2 := by decide
  have hm4 : (4 : Fin 6) - 1 = 3 := by decide
  have hm5 : (5 : Fin 6) - 1 = 4 := by decide
  have hw : w = ![w 0, w 1, w 2, w 3, w 4, w 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hw] at hAcount hHcount hLcount hflank hpair hcost
  revert hAcount hHcount hLcount hflank
  cases h0 : w 0 <;> cases h1 : w 1 <;>
    cases h2 : w 2 <;> cases h3 : w 3 <;>
    cases h4 : w 4 <;> cases h5 : w 5 <;>
    intro hAcount hHcount hLcount hflank
  all_goals
    simp [classCount, bothCoreHighLow] at hAcount hHcount hLcount hflank
    try contradiction
  all_goals
    have hp0 := hpair 0
    have hp1 := hpair 1
    have hp2 := hpair 2
    have hp3 := hpair 3
    have hp4 := hpair 4
    have hp5 := hpair 5
    have hg0 := hcost 0
    have hg1 := hcost 1
    have hg2 := hcost 2
    have hg3 := hcost 3
    have hg4 := hcost 4
    have hg5 := hcost 5
    simp [classGapCost, h0, h1, h2, h3, h4, h5,
      hm0, hm1, hm2, hm3, hm4, hm5] at hp0 hp1 hp2 hp3 hp4 hp5 hg0 hg1 hg2 hg3 hg4 hg5
    nlinarith [Real.pi_pos]

/-- The actual six-center class order is the candidate AHAHLL orbit once
the paired core-angle estimate is combined with the exhaustive word
classifier and the actual distinct blocker adjacency matching. -/
theorem distinct_six_order_word_AHAHLL
    (q : Fin 6 → Plane) (hsep : Separated q 2)
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (w : Fin 6 → M2Kind)
    (hAcount : classCount w .A = 2)
    (hHcount : classCount w .H = 2)
    (hLcount : classCount w .L = 2)
    (hArad : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hHrad : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hLrad : ∀ i, w i = .L →
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (hmatch : matchedAdjacentHighs w)
    (hbudget : classBudget w ≤ 3600) :
    dihedralEquivalent w wordAHAHLL := by
  apply distinct_class_word_single_orbit w hAcount hHcount hLcount
    hbudget hmatch
  intro hflank
  exact distinct_both_core_high_low_impossible q hsep φ hmono harg
    hfirst hlast w hAcount hHcount hLcount hArad hHrad hLrad hflank

end CP15
