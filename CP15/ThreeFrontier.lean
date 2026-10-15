import CP15.FourFrontier
import CP15.K10m1Closed

namespace CP15

def ThreeResidualRows (K m : ℕ) : Prop :=
  (K = 8 ∧ m = 1) ∨ (K = 9 ∧ m = 1) ∨ (K = 10 ∧ m = 0)

theorem SelectedPacking15.three_rows {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b) :
    ThreeResidualRows (boundarySet p b).card (nonOuterIndices p b).card := by
  rcases h.four_rows with ⟨hK, hm⟩ | ⟨hK, hm⟩ | ⟨hK, hm⟩ | ⟨hK, hm⟩
  · exact Or.inl ⟨hK, hm⟩
  · exact Or.inr (Or.inl ⟨hK, hm⟩)
  · exact Or.inr (Or.inr ⟨hK, hm⟩)
  · exact False.elim (h.K10m1_impossible hK hm)

theorem exists_selectedPacking15_at_three_rows :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane, SelectedPacking15 p b ∧
      ThreeResidualRows (boundarySet p b).card (nonOuterIndices p b).card := by
  obtain ⟨b, p, h⟩ := exists_selectedPacking15
  exact ⟨b, p, h, h.three_rows⟩

end CP15
