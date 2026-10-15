import CP15.CandidateFeasible
import CP15.CandidateBounds
import CP15.MainReduction

namespace CP15

/-- An unconditional, formally checked lower bound for the original problem. -/
theorem candidate_lower_bound : 2 / candidateB ≤ originalValue := by
  have hf : PointFeasible 15 (2 / candidateB) :=
    scale_center_to_point candidateB_pos Candidate.center_feasible
  rw [originalValue_eq_d15]
  exact le_csSup
    ⟨2, fun _ hd => pointFeasible_le_two hd⟩ hf

/-- The exact candidate feasibility now discharges the sole premise in the
radial-cap selection theorem. The resulting radius `b` is optimal, but its
equality with `candidateB` is not established here. -/
theorem exists_optimal_selected :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane,
      b ≤ candidateB ∧ CenterOptimal 15 b ∧
      InDisk b p ∧ Separated p 2 ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) :=
  exists_optimal_selected_from_candidate Candidate.center_feasible

/-- The selected optimal representative has a non-outer cap strictly below
the four-point threshold `sqrt 2`. The geometric four-point obstruction and
later case splits remain separate proof obligations. -/
theorem exists_optimal_selected_with_small_F :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane,
      b ≤ candidateB ∧ CenterOptimal 15 b ∧
      InDisk b p ∧ Separated p 2 ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) ∧
      F b < Real.sqrt 2 := by
  obtain ⟨b, p, hbB, hopt, hp, hs, hD, hF⟩ := exists_optimal_selected
  have hb : 2 < b := centerFeasible_radius_gt_two hopt.1
  exact ⟨b, p, hbB, hopt, hp, hs, hD, hF,
    Candidate.F_lt_sqrt_two_of_le_candidateB hb hbB⟩

end CP15
