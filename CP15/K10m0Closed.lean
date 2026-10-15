import CP15.SelectedK10Model
import CP15.K10CanonicalClosed

namespace CP15

/-- The last actual-packing case, with every occupancy orbit and every
closed radius region covered. No independent certificate premise remains. -/
theorem SelectedPacking15.K10m0_lower_bound
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10) (hm : (nonOuterIndices p b).card = 0) :
    candidateB ≤ b := by
  obtain ⟨r, empty, g, hmodel⟩ := h.K10m0_cyclic_model hK hm
  obtain ⟨pat, r', g', hc⟩ := hmodel.exists_canonical
  have hb : 3 < b := by
    have hh := h.elementaryLower
    have hs : 2 < Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
    linarith
  exact k10_canonical_model_lower pat b r' g' hb h.belowCandidate hc

end CP15
