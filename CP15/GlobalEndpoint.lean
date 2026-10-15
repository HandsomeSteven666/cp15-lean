import CP15.OneFrontier
import CP15.K10m0Closed
import CP15.K10EndpointEquality
import CP15.AlternatingGeometry
import CP15.DifferenceCertificate
import CP15.ClosedBoxCertificate
import CP15.OddCycleLocal

namespace CP15

/-- Compatibility interface for the last global case. Its concrete
value below is supplied by the complete actual-packing proof. -/
structure ResidualExclusions15 : Prop where
  K10m0 : ∀ p b, SelectedPacking15 p b →
    (boundarySet p b).card = 10 → (nonOuterIndices p b).card = 0 →
      candidateB ≤ b

/-- Complete logical assembly after (and only after) the residual geometric
and certificate obligations have been proved. Its remaining premise is
visible in the theorem type and is not replaced by an axiom or `sorry`. -/
theorem centerOptimal_candidate_of_residualExclusions
    (closure : ResidualExclusions15) : CenterOptimal 15 candidateB := by
  obtain ⟨b, p, h, hK, hm⟩ := exists_selectedPacking15_at_K10m0
  have hlower : candidateB ≤ b := closure.K10m0 p b h hK hm
  have heq : b = candidateB := le_antisymm h.belowCandidate hlower
  simpa [heq] using h.optimal

theorem originalValue_eq_candidate_of_residualExclusions
    (closure : ResidualExclusions15) : originalValue = 2 / candidateB :=
  originalValue_eq_candidate_of_centerOptimal
    (centerOptimal_candidate_of_residualExclusions closure)

/-- The last field is discharged by the actual-packing theorem, without
an external certificate premise. -/
theorem residualExclusions15_closed : ResidualExclusions15 :=
  ⟨fun _ _ h hK hm => h.K10m0_lower_bound hK hm⟩

/-- Unconditional optimality of the exact fifteen-center candidate. -/
theorem centerOptimal_candidate : CenterOptimal 15 candidateB :=
  centerOptimal_candidate_of_residualExclusions residualExclusions15_closed

/-- For an arbitrary optimal packing with ten boundary centers, ten is
automatically the maximum boundary count.  Thus the radial cap does not
need the selection argument in this branch. -/
theorem optimal_ten_boundary_inner_cap (p : Fin 15 → Plane) (b : ℝ)
    (hopt : CenterOptimal 15 b) (hpack : InDisk b p ∧ Separated p 2)
    (hK : (boundarySet p b).card = 10) :
    ∀ i, ‖p i‖ < b → ‖p i‖ < D b := by
  have hbB : b ≤ candidateB := hopt.2 candidateB centerOptimal_candidate.1
  have hb : 2 < b := centerFeasible_radius_gt_two hopt.1
  have hmax : MaxBoundaryCount p b := by
    intro q _ hqsep
    have hbound := boundary_count_le_ten q b (by linarith) hbB hqsep
    omega
  exact inner_cap_of_noBoundaryReplacement p b hb hpack
    (noBoundaryReplacement_of_maxBoundaryCount p b hmax)

/-- Equality conditions for any optimal packing whose actual polar order is
the alternating order and whose five inner radii lie in the certified local
cube.  No extremal representative is selected in this statement. -/
theorem optimal_alternating_gap_equalities (q : Fin 15 → Plane) (b : ℝ)
    (φ : Fin 15 → ℝ) (hopt : CenterOptimal 15 b)
    (hframe : LiftedFifteenFrame q φ) (hsep : Separated q 2)
    (hleft : ∀ i, ‖q (alternatingLeft i)‖ = b)
    (hright : ∀ i, ‖q (alternatingRight i)‖ = b)
    (hr : ∀ i, ‖q (alternatingInner i)‖ ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    b = candidateB ∧
      (∀ i, ‖q (alternatingInner i)‖ = candidateInnerRadius) ∧
      (∀ i, forwardArc15 φ (alternatingLeft i) (alternatingInner i) =
        contactAngle candidateB candidateInnerRadius) ∧
      (∀ i, forwardArc15 φ (alternatingInner i) (alternatingRight i) =
        contactAngle candidateB candidateInnerRadius) ∧
      (∀ i, forwardArc15 φ (alternatingRight i) (alternatingLeft (i + 1)) =
        outerAlpha candidateB) := by
  have hbEq : b = candidateB :=
    le_antisymm (hopt.2 candidateB centerOptimal_candidate.1)
      (centerOptimal_candidate.2 b hopt.1)
  exact local_alternating_packing_gap_equalities q b φ hframe hsep
    (by rw [hbEq]; linarith [candidateB_local_bounds.1]) hbEq.le
    hleft hright hr

/-- End-to-end equality for the original unit-disk point objective. -/
theorem originalValue_eq_candidate : originalValue = 2 / candidateB :=
  originalValue_eq_candidate_of_residualExclusions residualExclusions15_closed

/-- An unconditional kernel-checked interval for the original objective.
The upper endpoint is the independent elementary radius bound; it is
weaker than the claimed candidate equality. -/
theorem originalValue_elementary_interval :
    2 / candidateB ≤ originalValue ∧ originalValue ≤ 2 / (1 + Real.sqrt 5) := by
  refine ⟨candidate_lower_bound, ?_⟩
  obtain ⟨b, p, h⟩ := exists_selectedPacking15
  have hb : 0 < b := by
    have hc := h.elementaryLower
    nlinarith [Real.sqrt_nonneg 5]
  have hc : 0 < 1 + Real.sqrt 5 := by positivity
  have hv : originalValue = 2 / b := by
    rw [originalValue_eq_d15]
    exact d15_eq_of_pointOptimal (center_optimal_to_point_optimal hb h.optimal)
  rw [hv]
  exact (div_le_div_iff₀ hb hc).2 (by nlinarith [h.elementaryLower])

end CP15
