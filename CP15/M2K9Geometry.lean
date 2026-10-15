import CP15.M2K9SharedGap

namespace CP15

/-- Exact partition of the fifteen centers by boundary status and outer
contact. This is the counting bridge for the six-center inner ring in the
`K=9,m=2` analysis. -/
theorem boundary_nonOuter_touching_card_partition
    (p : Fin 15 → Plane) (b : ℝ) (hpack : InDisk b p) :
    (boundarySet p b).card + (nonOuterIndices p b).card +
      (touchingInnerSet p b).card = 15 := by
  classical
  let B := boundarySet p b
  let M := nonOuterIndices p b
  let T := touchingInnerSet p b
  have hcover : B ∪ M ∪ T = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases heq : ‖p i‖ = b
    · left; left; simpa [B, boundarySet] using heq
    · have hlt : ‖p i‖ < b := lt_of_le_of_ne (hpack i) heq
      by_cases ht : TouchesOuter p b i
      · right; simpa [T, touchingInnerSet] using And.intro hlt ht
      · left; right
        simpa [M, nonOuterIndices] using And.intro hlt ht
  have hBM : Disjoint B M := by
    apply Finset.disjoint_left.mpr
    intro i hiB hiM
    have hbd : ‖p i‖ = b := by simpa [B, boundarySet] using hiB
    have hlt : ‖p i‖ < b :=
      (by simpa [M, nonOuterIndices] using hiM :
        ‖p i‖ < b ∧ ¬TouchesOuter p b i).1
    exact (ne_of_lt hlt) hbd
  have hBMT : Disjoint (B ∪ M) T := by
    apply Finset.disjoint_left.mpr
    intro i hiBM hiT
    have hiT' : ‖p i‖ < b ∧ TouchesOuter p b i := by
      simpa [T, touchingInnerSet] using hiT
    rcases Finset.mem_union.mp hiBM with hiB | hiM
    · have hbd : ‖p i‖ = b := by simpa [B, boundarySet] using hiB
      exact (ne_of_lt hiT'.1) hbd
    · have hiM' : ‖p i‖ < b ∧ ¬TouchesOuter p b i := by
        simpa [M, nonOuterIndices] using hiM
      exact hiM'.2 hiT'.2
  have hcardBM := Finset.card_union_of_disjoint hBM
  have hcardBMT := Finset.card_union_of_disjoint hBMT
  rw [hcover] at hcardBMT
  simp only [Finset.card_univ, Fintype.card_fin] at hcardBMT
  dsimp [B, M, T] at hcardBM hcardBMT
  omega

theorem k9_m2_touching_inner_card_four
    (p : Fin 15 → Plane) (b : ℝ) (hpack : InDisk b p)
    (hK : (boundarySet p b).card = 9)
    (hm : (nonOuterIndices p b).card = 2) :
    (touchingInnerSet p b).card = 4 := by
  have hpart := boundary_nonOuter_touching_card_partition p b hpack
  omega

end CP15
