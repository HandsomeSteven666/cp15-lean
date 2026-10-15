import CP15.BasicAngleBounds

namespace CP15

/-- Finite-sum part of the short-gap theorem. The geometric construction of
the cyclic gaps is deliberately a separate obligation. -/
theorem ring_gaps_lt_pi_of_lower_bound {n : ℕ} (hn : 9 ≤ n)
    (α : ℝ) (hα : 0 ≤ α) (h8 : Real.pi < 8 * α)
    (g : Fin n → ℝ)
    (hlower : ∀ i, α ≤ g i)
    (hsum : (∑ i : Fin n, g i) = 2 * Real.pi) :
    ∀ i, g i < Real.pi := by
  intro i
  let s : Finset (Fin n) := Finset.univ.erase i
  have hs_card : 8 ≤ s.card := by
    dsimp [s]
    simp
    omega
  have hconst : (s.card : ℝ) * α ≤ ∑ j ∈ s, g j := by
    calc
      (s.card : ℝ) * α = ∑ j ∈ s, α := by simp
      _ ≤ ∑ j ∈ s, g j := by
        apply Finset.sum_le_sum
        intro j hj
        exact hlower j
  have heightr : (8 : ℝ) * α ≤ ∑ j ∈ s, g j := by
    have hcast : (8 : ℝ) ≤ s.card := by exact_mod_cast hs_card
    exact (mul_le_mul_of_nonneg_right hcast hα).trans hconst
  have hdecomp : (∑ j : Fin n, g j) =
      (∑ j ∈ s, g j) + g i := by
    simpa [s] using (Finset.sum_erase_add Finset.univ g
      (Finset.mem_univ i)).symm
  rw [hsum] at hdecomp
  linarith

/-- At the CP15 candidate scale, the preceding finite-sum theorem applies
to any proposed cyclic ring gaps satisfying the explicit premises. -/
theorem candidate_ring_gaps_lt_pi {n : ℕ} (hn : 9 ≤ n)
    (b : ℝ) (hb : 2 < b) (hbB : b ≤ candidateB)
    (g : Fin n → ℝ)
    (hlower : ∀ i, outerAlpha b ≤ g i)
    (hsum : (∑ i : Fin n, g i) = 2 * Real.pi) :
    ∀ i, g i < Real.pi := by
  have hα0 : 0 ≤ outerAlpha b := by
    have h := outerAlpha_ge_two_div b (by linarith)
    have htwo : 0 ≤ 2 / b := by positivity
    linarith
  exact ring_gaps_lt_pi_of_lower_bound hn (outerAlpha b) hα0
    (eight_outerAlpha_gt_pi b hb hbB) g hlower hsum

end CP15
