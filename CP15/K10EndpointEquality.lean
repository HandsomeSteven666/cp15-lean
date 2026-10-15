import CP15.K10CanonicalClosed
import CP15.SelectedK10Model

namespace CP15

set_option maxHeartbeats 0

/-- The equality classification returned by the checked K=10 scalar cover,
transported back from its dihedral canonical representative.  This theorem
applies to every cyclic inner model, independently of extremal selection. -/
theorem k10_cyclic_model_endpoint_equality (b : ℝ) (r : Fin 5 → ℝ)
    (empty : Fin 5 → ℕ) (g : Fin 5 → ℝ)
    (hb : 3 < b) (hbB : b ≤ candidateB)
    (h : CyclicInnerModel b r empty g) :
    b = candidateB ∧ (∀ i, empty i = 1) ∧
      (∀ i, r i = candidateInnerRadius) ∧
      (∀ i, g i = 2 * Real.pi / 5) := by
  have hempty (i : Fin 5) : empty i ≤ 5 := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
      Nat.zero_le (empty j)) (Finset.mem_univ i)
    simpa only [h.empty_sum] using hh
  let w : Fin 5 → Fin 6 := fun i => ⟨empty i, by have hh := hempty i; omega⟩
  have hw : (∑ i, (w i).val) = 5 := h.empty_sum
  obtain ⟨p, a, reflected, hp⟩ := k10_empty_orbit_checked w hw
  have hbase : b = candidateB ∧ (∀ i, empty i = 1) ∧
      (∀ i, r i = candidateInnerRadius) := by
    cases reflected
    · have hc := h.rotate a
      have heq : (fun i => empty (i + a)) = k10EmptyPattern p := by
        funext i
        simpa [w] using hp i
      rw [heq] at hc
      have hcert := k10_canonical_model_equality p b
        (fun i => r (i + a)) (fun i => g (i + a)) hb hbB hc
      refine ⟨hcert.1, ?_, ?_⟩
      · intro i
        have hh := congrFun hcert.2.1 (i - a)
        rw [← heq] at hh
        simpa only [show (i - a) + a = i by abel] using hh
      · intro i
        have hh := hcert.2.2 (i - a)
        simpa only [show (i - a) + a = i by abel] using hh
    · have hc := h.reflect a
      have heq : (fun i => empty (a - i - 1)) = k10EmptyPattern p := by
        funext i
        simpa [w] using hp i
      rw [heq] at hc
      have hcert := k10_canonical_model_equality p b
        (fun i => r (a - i)) (fun i => g (a - i - 1)) hb hbB hc
      refine ⟨hcert.1, ?_, ?_⟩
      · intro i
        have hh := congrFun hcert.2.1 (a - i - 1)
        rw [← heq] at hh
        simpa only [show a - (a - i - 1) - 1 = i by abel] using hh
      · intro i
        have hh := hcert.2.2 (a - i)
        simpa only [show a - (a - i) = i by abel] using hh
  obtain ⟨hbEq, heEq, hrEq⟩ := hbase
  have hglower (i : Fin 5) : 2 * Real.pi / 5 ≤ g i := by
    have hs := h.support i 1 (by decide)
    norm_num [fiveArc] at hs
    rw [heEq i, hrEq i, hrEq (i + 1), hbEq] at hs
    calc
      2 * Real.pi / 5 = outerAlpha candidateB +
          2 * contactAngle candidateB candidateInnerRadius :=
        candidate_outer_inner_angle_balance.symm
      _ = contactAngle candidateB candidateInnerRadius +
          contactAngle candidateB candidateInnerRadius + (1 : ℝ) * outerAlpha candidateB := by ring
      _ ≤ g i := by simpa using hs
  let slack : Fin 5 → ℝ := fun i => g i - 2 * Real.pi / 5
  have hslack0 (i : Fin 5) : 0 ≤ slack i := by dsimp [slack]; linarith [hglower i]
  have hsum : (∑ i, slack i) = 0 := by
    simp only [slack, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, h.gap_sum]
    ring
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => hslack0 i)).1 hsum
  exact ⟨hbEq, heEq, hrEq, fun i => by
    have hi := hz i (Finset.mem_univ i)
    dsimp [slack] at hi
    linarith⟩

/-- Equality information for the actual selected K=10,m=0 packing, carried
by its five-center cyclic model rather than only by the radius bound. -/
theorem SelectedPacking15.K10m0_scalar_equality
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10)
    (hm : (nonOuterIndices p b).card = 0) :
    ∃ r : Fin 5 → ℝ, ∃ empty : Fin 5 → ℕ, ∃ g : Fin 5 → ℝ,
      CyclicInnerModel b r empty g ∧
      b = candidateB ∧ (∀ i, empty i = 1) ∧
        (∀ i, r i = candidateInnerRadius) ∧
        (∀ i, g i = 2 * Real.pi / 5) := by
  obtain ⟨r, empty, g, hmodel⟩ := h.K10m0_cyclic_model hK hm
  have hb : 3 < b := by
    have hs : 2 < Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
    linarith [h.elementaryLower]
  exact ⟨r, empty, g, hmodel,
    k10_cyclic_model_endpoint_equality b r empty g hb h.belowCandidate hmodel⟩

/-- Equality is transported back to the actual five inner centers and
their actual lifted angles. The original index map and occupied outer-gap
indices are retained, unlike the scalar-only endpoint theorem. -/
theorem SelectedPacking15.K10m0_actual_inner_equalities
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10)
    (hm : (nonOuterIndices p b).card = 0) :
    ∃ ix : Fin 5 → Fin 15, ∃ u : Fin 5 → Fin 10,
      ∃ φ : Fin 5 → ℝ, ∃ ψ : Fin 10 → ℝ,
      Function.Injective ix ∧ StrictMono u ∧
      (∀ i, ‖p (ix i)‖ < b) ∧
      (∀ i, ‖p (ix i)‖ = candidateInnerRadius) ∧
      (∀ i, occupiedEmptyCount u i = 1) ∧
      (∀ i, cyclicAngleGap φ i = 2 * Real.pi / 5) ∧
      (∀ i, φ i = polarArg (p (ix i)) ∨
        φ i = polarArg (p (ix i)) + 2 * Real.pi) ∧
      (∀ i, ψ (u i) + contactAngle b ‖p (ix i)‖ ≤ φ i) ∧
      (∀ i, φ i ≤ ψ (u i) + cyclicAngleGap ψ (u i) -
        contactAngle b ‖p (ix i)‖) ∧
      (∀ k, outerAlpha b ≤ cyclicAngleGap ψ k) ∧
      StrictMono ψ ∧ (∀ k, ψ k ∈ boundaryAngles p b) := by
  obtain ⟨ix, u, φ, ψ, hix, hu, hinner, hphase, hleft, hright, hα,
    hψmono, hψmem,
    hmodel⟩ := h.K10m0_cyclic_model_actual hK hm
  have hb : 3 < b := by
    have hs : 2 < Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
    linarith [h.elementaryLower]
  obtain ⟨_, hempty, hr, hg⟩ :=
    k10_cyclic_model_endpoint_equality b
      (fun i => ‖p (ix i)‖) (occupiedEmptyCount u)
      (cyclicAngleGap φ) hb h.belowCandidate hmodel
  exact ⟨ix, u, φ, ψ, hix, hu, hinner, hr, hempty, hg,
    hphase, hleft, hright, hα, hψmono, hψmem⟩

end CP15
