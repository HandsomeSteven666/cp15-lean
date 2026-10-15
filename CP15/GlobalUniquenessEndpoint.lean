import CP15.ActualOuterCycle
import CP15.UniqueExtensionOrbit
import CP15.GlobalUniquenessOrbitTransport
import CP15.GlobalUniquenessTerminalReference

namespace CP15

open Filter Topology

/-- Once the candidate component is proved rigid and each candidate
boundary center has a unique feasible extension from the other fourteen,
every optimal fifteen center packing is congruent to the candidate. The
terminal representative required by this implication is now identified
from the actual equality coordinates. -/
theorem all_optimal_packings_congruent_of_candidate_rigidity_and_extension
    (hcandidateComponentRigidity :
      ∀ q : FeasiblePacking15 candidateB,
        CenteredCongruent15 q.1 Candidate.pointAtSeparationTwo →
        ∀ r, r ∈ connectedComponentIn (FeasibleSet15 candidateB) q.1 →
          CenteredCongruent15 r Candidate.pointAtSeparationTwo)
    (hunique : UniqueBoundaryPointFromOthers
      Candidate.pointAtSeparationTwo candidateB) :
    ∀ p : FeasiblePacking15 candidateB,
      CenteredCongruent15 p.1 Candidate.pointAtSeparationTwo := by
  apply all_optimal_packings_congruent_of_rep_rigidity_and_extension
  · exact terminal_component_congruent_to_candidate
  · exact hcandidateComponentRigidity
  · exact hunique

/-- The boundary-extension part of the global argument is now unconditional.
Connected-component rigidity remains the only explicit geometric hypothesis
in this endpoint. -/
theorem all_optimal_packings_congruent_of_candidate_component_rigidity
    (hcandidateComponentRigidity :
      ∀ q : FeasiblePacking15 candidateB,
        CenteredCongruent15 q.1 Candidate.pointAtSeparationTwo →
        ∀ r, r ∈ connectedComponentIn (FeasibleSet15 candidateB) q.1 →
          CenteredCongruent15 r Candidate.pointAtSeparationTwo) :
    ∀ p : FeasiblePacking15 candidateB,
      CenteredCongruent15 p.1 Candidate.pointAtSeparationTwo := by
  exact all_optimal_packings_congruent_of_candidate_rigidity_and_extension
    hcandidateComponentRigidity candidate_unique_boundary_extension

/-- A single strictly ordered feasible alternating reference, together with
the local radius margins, now suffices for the unconditional component
argument: its neighborhood isolates the closed candidate orbit, and the
relative clopen argument supplies component rigidity at every orbit point. -/
theorem all_optimal_packings_congruent_of_local_alternating_reference
    (r : Fin 15 → Plane)
    (hr : r ∈ FeasibleSet15 candidateB)
    (hmono : StrictMono (fun i => polarArg (r i)))
    (hcut : ∀ i, planeComplex (r i) ∈ Complex.slitPlane)
    (hleft : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingLeft i)‖)
    (hright : ∀ i, (17 / 5 : ℝ) < ‖r (alternatingRight i)‖)
    (hinnerLo : ∀ i, (1697 / 1000 : ℝ) < ‖r (alternatingInner i)‖)
    (hinnerHi : ∀ i, ‖r (alternatingInner i)‖ < (853 / 500 : ℝ)) :
    ∀ p : FeasiblePacking15 candidateB,
      CenteredCongruent15 p.1 Candidate.pointAtSeparationTwo := by
  obtain ⟨hrCongruent, hlocal⟩ :=
    localAlternatingReference_congruent_and_isolated r hr hmono hcut
      hleft hright hinnerLo hinnerHi
  have hrOrbit : r ∈ CandidateCongruenceOrbit15 := hrCongruent
  have hlocalOrbit : ∀ᶠ z : Fin 15 → Plane in 𝓝 r,
      z ∈ FeasibleSet15 candidateB → z ∈ CandidateCongruenceOrbit15 := by
    filter_upwards [hlocal] with z hz hzfeasible
    simpa [CandidateCongruenceOrbit15] using hz hzfeasible
  have hcomponentRigidity :
      ∀ q : FeasiblePacking15 candidateB,
        CenteredCongruent15 q.1 Candidate.pointAtSeparationTwo →
        ∀ x, x ∈ connectedComponentIn (FeasibleSet15 candidateB) q.1 →
          CenteredCongruent15 x Candidate.pointAtSeparationTwo := by
    intro q hq x hx
    exact connectedComponentIn_subset_orbit_of_local_reference
      r hrOrbit hlocalOrbit q.1 hq x hx
  exact all_optimal_packings_congruent_of_candidate_component_rigidity
    hcomponentRigidity

/-- Unconditional global uniqueness up to relabeling and an orthogonal
centered isometry: every feasible fifteen-center packing at the optimal
radius is congruent to the explicit candidate. -/
theorem global_unique_optimal_packing15 :
    ∀ p : FeasiblePacking15 candidateB,
      CenteredCongruent15 p.1 Candidate.pointAtSeparationTwo := by
  obtain ⟨r, hr, hmono, hcut, hleft, hright, hinnerLo, hinnerHi⟩ :=
    exists_candidate_localAlternatingReference
  exact all_optimal_packings_congruent_of_local_alternating_reference
    r hr hmono hcut hleft hright hinnerLo hinnerHi

end CP15
