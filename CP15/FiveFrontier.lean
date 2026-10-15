import CP15.M2Closed
import CP15.SevenTouchingClosed

namespace CP15

def FiveResidualRows (K m : ℕ) : Prop :=
  (K = 8 ∧ m = 1) ∨ (K = 9 ∧ m = 0) ∨ (K = 9 ∧ m = 1) ∨
    (K = 10 ∧ m = 0) ∨ (K = 10 ∧ m = 1)

theorem SelectedPacking15.five_rows {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b) :
    FiveResidualRows (boundarySet p b).card (nonOuterIndices p b).card := by
  have hs := h.seven_rows h.core_count_le_one
  rcases hs with ⟨hK, hm⟩ | ⟨hK, hm⟩ | ⟨hK, hm⟩ | ⟨hK, hm⟩ |
    ⟨hK, hm⟩ | ⟨hK, hm⟩ | ⟨hK, hm⟩
  · exact False.elim (h.K7m1_impossible hK hm)
  · exact False.elim (h.K8m0_impossible hK hm)
  · exact Or.inl ⟨hK, hm⟩
  · exact Or.inr (Or.inl ⟨hK, hm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hK, hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hK, hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hK, hm⟩)))

theorem exists_selectedPacking15_at_five_rows :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane, SelectedPacking15 p b ∧
      FiveResidualRows (boundarySet p b).card (nonOuterIndices p b).card := by
  obtain ⟨b, p, h⟩ := exists_selectedPacking15
  exact ⟨b, p, h, h.five_rows⟩

end CP15
