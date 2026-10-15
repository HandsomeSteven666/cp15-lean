import CP15.ThreeFrontier
import CP15.K8m1Closed
import CP15.K9m1Closed

namespace CP15

/-- Every selected optimum has ten boundary centers and no core center.
All other rows are excluded by unconditional actual-packing theorems. -/
theorem SelectedPacking15.only_K10m0 {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b) :
    (boundarySet p b).card = 10 ∧ (nonOuterIndices p b).card = 0 := by
  rcases h.three_rows with ⟨hK, hm⟩ | ⟨hK, hm⟩ | ⟨hK, hm⟩
  · exact False.elim (h.K8m1_impossible hK hm)
  · exact False.elim (h.K9m1_impossible hK hm)
  · exact ⟨hK, hm⟩

theorem exists_selectedPacking15_at_K10m0 :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane, SelectedPacking15 p b ∧
      (boundarySet p b).card = 10 ∧ (nonOuterIndices p b).card = 0 := by
  obtain ⟨b, p, h⟩ := exists_selectedPacking15
  exact ⟨b, p, h, h.only_K10m0⟩

end CP15
