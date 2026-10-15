import CP15.FiveFrontier
import CP15.K9m0Closed

namespace CP15

def FourResidualRows (K m : ℕ) : Prop :=
  (K = 8 ∧ m = 1) ∨ (K = 9 ∧ m = 1) ∨
    (K = 10 ∧ m = 0) ∨ (K = 10 ∧ m = 1)

theorem SelectedPacking15.four_rows {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b) :
    FourResidualRows (boundarySet p b).card (nonOuterIndices p b).card := by
  rcases h.five_rows with ⟨hK, hm⟩ | ⟨hK, hm⟩ | ⟨hK, hm⟩ | ⟨hK, hm⟩ | ⟨hK, hm⟩
  · exact Or.inl ⟨hK, hm⟩
  · exact False.elim (h.K9m0_impossible hK hm)
  · exact Or.inr (Or.inl ⟨hK, hm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hK, hm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hK, hm⟩))

theorem exists_selectedPacking15_at_four_rows :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane, SelectedPacking15 p b ∧
      FourResidualRows (boundarySet p b).card (nonOuterIndices p b).card := by
  obtain ⟨b, p, h⟩ := exists_selectedPacking15
  exact ⟨b, p, h, h.four_rows⟩

end CP15
