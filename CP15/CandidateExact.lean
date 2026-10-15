import CP15.CandidateFeasible
import CP15.Replacement

namespace CP15.Candidate

theorem rho_pos : 0 < rho := by
  have h := two_rho_eq_candidateB
  have hb := CP15.candidateB_pos
  linarith

/-- The constructed fifteen points have attained minimum distance exactly
one at the working scale. The lower bound uses all 105 pair checks; the
upper bound uses the explicit first contact. -/
theorem minDistance_point_eq_one : minDistance point = 1 := by
  apply le_antisymm
  · exact csInf_le (pairDistances_bddBelow point)
      ⟨0, 1, by decide, first_outer_contact.symm⟩
  · exact (separated_iff_le_minDistance point 1).1 separated_point

/-- The candidate in the original unit-disk point-packing normalization. -/
noncomputable def unitPoint : Fin 15 → Plane := scale (1 / rho) point

theorem unitPoint_in_disk : InUnitDisk unitPoint := by
  intro i
  change ‖scale (1 / rho) point i‖ ≤ 1
  rw [norm_scale (1 / rho) (by positivity [rho_pos])]
  have h := all_radius_le i
  apply (mul_le_mul_of_nonneg_left h (by positivity [rho_pos])).trans
  field_simp [ne_of_gt rho_pos]
  norm_num

theorem unitPoint_separated : Separated unitPoint (1 / rho) := by
  intro i j hij
  change 1 / rho ≤ dist (scale (1 / rho) point i)
    (scale (1 / rho) point j)
  rw [dist_scale (1 / rho) (by positivity [rho_pos])]
  have h := separated_point i j hij
  nlinarith [mul_nonneg (show 0 ≤ 1 / rho by positivity [rho_pos])
    (sub_nonneg.mpr h)]

theorem minDistance_unitPoint_eq_inv_rho :
    minDistance unitPoint = 1 / rho := by
  apply le_antisymm
  · have hfirst : dist (unitPoint 0) (unitPoint 1) = 1 / rho := by
      change dist (scale (1 / rho) point 0) (scale (1 / rho) point 1) = _
      rw [dist_scale (1 / rho) (by positivity [rho_pos]), first_outer_contact]
      ring
    exact csInf_le (pairDistances_bddBelow unitPoint)
      ⟨0, 1, by decide, hfirst.symm⟩
  · exact (separated_iff_le_minDistance unitPoint (1 / rho)).1
      unitPoint_separated

theorem unitPoint_realizes_candidate_value :
    InUnitDisk unitPoint ∧
      minDistance unitPoint = 2 / CP15.candidateB := by
  constructor
  · exact unitPoint_in_disk
  · rw [minDistance_unitPoint_eq_inv_rho, ← two_rho_eq_candidateB]
    field_simp

def outerIndices : Finset (Fin 15) :=
  {0, 1, 2, 3, 6, 7, 11, 12, 13, 14}

private theorem norm_eq_rho_of_sq (i : Fin 15)
    (h : ‖point i‖ ^ 2 = rho ^ 2) : ‖point i‖ = rho := by
  nlinarith [norm_nonneg (point i), rho_pos.le]

private theorem norm_ne_rho_of_inner_sq (i : Fin 15)
    (h : ‖point i‖ ^ 2 = t ^ 2) : ‖point i‖ ≠ rho := by
  intro heq
  rw [heq] at h
  linarith [inner_radius_lt]

/-- Exactly ten indices attain the working-scale enclosing radius. -/
theorem point_on_boundary_iff (i : Fin 15) :
    ‖point i‖ = rho ↔ i ∈ outerIndices := by
  fin_cases i
  · simpa [outerIndices] using norm_eq_rho_of_sq 0 radius_sq_00
  · simpa [outerIndices] using norm_eq_rho_of_sq 1 radius_sq_01
  · simpa [outerIndices] using norm_eq_rho_of_sq 2 radius_sq_02
  · simpa [outerIndices] using norm_eq_rho_of_sq 3 radius_sq_03
  · simpa [outerIndices] using norm_ne_rho_of_inner_sq 4 radius_sq_04
  · simpa [outerIndices] using norm_ne_rho_of_inner_sq 5 radius_sq_05
  · simpa [outerIndices] using norm_eq_rho_of_sq 6 radius_sq_06
  · simpa [outerIndices] using norm_eq_rho_of_sq 7 radius_sq_07
  · simpa [outerIndices] using norm_ne_rho_of_inner_sq 8 radius_sq_08
  · simpa [outerIndices] using norm_ne_rho_of_inner_sq 9 radius_sq_09
  · simpa [outerIndices] using norm_ne_rho_of_inner_sq 10 radius_sq_10
  · simpa [outerIndices] using norm_eq_rho_of_sq 11 radius_sq_11
  · simpa [outerIndices] using norm_eq_rho_of_sq 12 radius_sq_12
  · simpa [outerIndices] using norm_eq_rho_of_sq 13 radius_sq_13
  · simpa [outerIndices] using norm_eq_rho_of_sq 14 radius_sq_14

theorem unitPoint_on_boundary_iff (i : Fin 15) :
    ‖unitPoint i‖ = 1 ↔ i ∈ outerIndices := by
  have hnorm : ‖unitPoint i‖ = ‖point i‖ / rho := by
    change ‖scale (1 / rho) point i‖ = _
    rw [norm_scale (1 / rho) (by positivity [rho_pos])]
    ring
  rw [hnorm]
  constructor
  · intro h
    have heq : ‖point i‖ = rho := by
      have h' := (div_eq_iff (ne_of_gt rho_pos)).1 h
      simpa using h'
    exact (point_on_boundary_iff i).1 heq
  · intro h
    rw [(point_on_boundary_iff i).2 h]
    exact div_self (ne_of_gt rho_pos)

theorem boundarySet_pointAtSeparationTwo_eq :
    boundarySet pointAtSeparationTwo CP15.candidateB = outerIndices := by
  ext i
  simp only [boundarySet, Finset.mem_filter, Finset.mem_univ, true_and]
  change ‖scale 2 point i‖ = CP15.candidateB ↔ i ∈ outerIndices
  rw [norm_scale 2 (by norm_num), ← two_rho_eq_candidateB]
  constructor
  · intro h
    apply (point_on_boundary_iff i).1
    linarith
  · intro h
    have hi := (point_on_boundary_iff i).2 h
    linarith

theorem boundarySet_pointAtSeparationTwo_card :
    (boundarySet pointAtSeparationTwo CP15.candidateB).card = 10 := by
  rw [boundarySet_pointAtSeparationTwo_eq]
  decide

end CP15.Candidate
