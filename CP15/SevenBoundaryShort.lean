import CP15.StrongOuterGap

namespace CP15.SevenBoundary

/-- All actual cyclic boundary gaps are shorter than a semicircle as soon
as there are seven boundary centers. The six other gaps are retained. -/
theorem every_next_gap_lt_pi (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 7 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card) :
    nextBoundaryGap p b
      (by rw [boundaryAngles_card p b hsep]; omega) u < Real.pi := by
  let hs : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  have hK' : 7 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    exact hK
  have hother := Finset.sum_le_sum (s := Finset.univ.erase u)
    (fun v _ => every_next_gap_ge_four_sevenths p b hb hbB hsep hs v)
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hother
  have hcount : (6 : ℝ) ≤ ((boundaryAngles p b).card - 1 : ℕ) := by
    exact_mod_cast (by omega : 6 ≤ (boundaryAngles p b).card - 1)
  have hsum := sum_next_boundary_gaps p b hs
  rw [← Finset.add_sum_erase Finset.univ (nextBoundaryGap p b hs)
    (Finset.mem_univ u)] at hsum
  nlinarith [Real.pi_lt_d6]

theorem ordered_boundary_adjacent_gap_lt_pi (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 7 ≤ (boundarySet p b).card)
    (i : Fin (boundaryAngles p b).card)
    (hi : i.val + 1 < (boundaryAngles p b).card) :
    (boundaryAngles p b).orderEmbOfFin rfl ⟨i.val + 1, hi⟩ -
      (boundaryAngles p b).orderEmbOfFin rfl i < Real.pi := by
  simpa [nextBoundaryGap, hi] using every_next_gap_lt_pi p b hb hbB hsep hK i

theorem ordered_boundary_wrap_gap_lt_pi (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 7 ≤ (boundarySet p b).card) :
    (boundaryAngles p b).orderEmbOfFin rfl ⟨0, by
      rw [boundaryAngles_card p b hsep]; omega⟩ + 2 * Real.pi -
    (boundaryAngles p b).orderEmbOfFin rfl
      ⟨(boundaryAngles p b).card - 1, by
        rw [boundaryAngles_card p b hsep]; omega⟩ < Real.pi := by
  have hs : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  have hn : ¬ (boundaryAngles p b).card - 1 + 1 < (boundaryAngles p b).card := by
    omega
  simpa [nextBoundaryGap, hn] using every_next_gap_lt_pi p b hb hbB hsep hK
    ⟨(boundaryAngles p b).card - 1, by omega⟩

end CP15.SevenBoundary
