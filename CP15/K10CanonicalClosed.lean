import CP15.K10CoverChunk23
import CP15.K10AlphaBound

namespace CP15
set_option maxHeartbeats 0

/-- Every canonical occupancy word is covered by its concrete closed tree. -/
theorem k10_canonical_model_equality (p : Fin 16) (b : ℝ) (r g : Fin 5 → ℝ)
    (hb : 3 < b) (hbC : b ≤ candidateB)
    (h : CyclicInnerModel b r (k10EmptyPattern p) g) :
    b = candidateB ∧ k10EmptyPattern p = (fun _ => 1) ∧
      (∀ i, r i = candidateInnerRadius) := by
  have hα := k10_outerAlpha_lower b hb hbC
  fin_cases p
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 0) 57580 628320
      k10p0chunk0Box k10p0chunk0Tree k10p0chunk0Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p0chunk0Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 1) 57580 628320
      k10p1chunk1Box k10p1chunk1Tree k10p1chunk1Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p1chunk1Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 2) 57580 628320
      k10p2chunk2Box k10p2chunk2Tree k10p2chunk2Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p2chunk2Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 3) 57580 628320
      k10p3chunk3Box k10p3chunk3Tree k10p3chunk3Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p3chunk3Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 4) 57580 628320
      k10p4chunk4Box k10p4chunk4Tree k10p4chunk4Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p4chunk4Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 5) 57580 628320
      k10p5chunk5Box k10p5chunk5Tree k10p5chunk5Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p5chunk5Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 6) 57580 628320
      k10p6chunk6Box k10p6chunk6Tree k10p6chunk6Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p6chunk6Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 7) 57580 628320
      k10p7chunk7Box k10p7chunk7Tree k10p7chunk7Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p7chunk7Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 8) 57580 628320
      k10p8chunk8Box k10p8chunk8Tree k10p8chunk8Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p8chunk8Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 9) 57580 628320
      k10p9chunk9Box k10p9chunk9Tree k10p9chunk9Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p9chunk9Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 10) 57580 628320
      k10p10chunk10Box k10p10chunk10Tree k10p10chunk10Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p10chunk10Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 11) 57580 628320
      k10p11chunk11Box k10p11chunk11Tree k10p11chunk11Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p11chunk11Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 12) 57580 628320
      k10p12chunk12Box k10p12chunk12Tree k10p12chunk12Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p12chunk12Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 13) 57580 628320
      k10p13chunk13Box k10p13chunk13Tree k10p13chunk13Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p13chunk13Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 14) 57580 628320
      k10p14chunk14Box k10p14chunk14Tree k10p14chunk14Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p14chunk14Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith
  · apply k10ModelCoverCheck_equality (k10EmptyPattern 15) 57588 628319
      k10p15chunk171Box k10p15chunk171Tree k10p15chunk171Checked b r g hb hbC h
    · intro i
      have hh := h.radius i
      fin_cases i <;> simpa [k10p15chunk171Box] using hh
    · norm_num
      nlinarith
    · norm_num
    · have hh := k10_turn_upper
      norm_num
      linarith

/-- The original value interface follows from the equality certificate. -/
theorem k10_canonical_model_lower (p : Fin 16) (b : ℝ) (r g : Fin 5 → ℝ)
    (hb : 3 < b) (hbC : b ≤ candidateB)
    (h : CyclicInnerModel b r (k10EmptyPattern p) g) : candidateB ≤ b :=
  (k10_canonical_model_equality p b r g hb hbC h).1.ge

end CP15
