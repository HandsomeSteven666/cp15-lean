import CP15

-- Mathematical interfaces printed in the article's theorem map.
#check CP15.SelectedPacking15.only_K10m0
#check CP15.SelectedPacking15.K10_injective_touching_gap_assignment
#check CP15.SelectedPacking15.K10m0_cyclic_model_actual
#check CP15.k10ModelCoverCheck_sound
#check CP15.k10_canonical_model_equality
#check CP15.candidate_expanded_angular_stability
#check CP15.SelectedPacking15.K10m0_actual_gap_equalities
#check CP15.terminal_component_selectedPacking15
#check CP15.candidate_unique_boundary_extension
#check CP15.centerOptimal_candidate
#check CP15.originalValue_eq_candidate
#check CP15.global_unique_optimal_packing15

-- Kernel dependency audits for all three unconditional endpoints.
#print axioms CP15.centerOptimal_candidate
#print axioms CP15.originalValue_eq_candidate
#print axioms CP15.global_unique_optimal_packing15
