import CP15.Caps
import CP15.GridBound
import CP15.OptimalExistence
import CP15.Global

namespace CP15

/-- The fully checked selection and radial-cap package for fifteen centers.
The sole premise is feasibility at some radius. -/
theorem selected15_radial_caps {b : ℝ}
    (h : CenterFeasible 15 b) :
    ∃ p : Fin 15 → Plane,
      InDisk b p ∧ Separated p 2 ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) :=
  exists_selected_with_F_cap (centerFeasible_radius_gt_two h) h

/-- Starting from a feasible candidate radius, select an actual radius
minimizer and then a representative satisfying both radial caps. -/
theorem exists_optimal_selected_from_candidate
    (h : CenterFeasible 15 candidateB) :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane,
      b ≤ candidateB ∧ CenterOptimal 15 b ∧
      InDisk b p ∧ Separated p 2 ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) := by
  obtain ⟨b, hbB, hopt⟩ := centerOptimal_exists_of_feasible h
  obtain ⟨p, hp, hs, hD, hF⟩ := selected15_radial_caps hopt.1
  exact ⟨b, p, hbB, hopt, hp, hs, hD, hF⟩

end CP15
