import CP15.TouchingCount
import CP15.M2K9SharedClosed
import CP15.M2K9DistinctHalfCutoff
import CP15.OrderedContactTransfer

open scoped InnerProductSpace

namespace CP15

/-- A single extremal representative with all the proved selection and
geometric premises retained. Every field is obtained below; this record
does not assume the candidate's optimality or any residual exclusion. -/
structure SelectedPacking15 (p : Fin 15 → Plane) (b : ℝ) : Prop where
  belowCandidate : b ≤ candidateB
  optimal : CenterOptimal 15 b
  inDisk : InDisk b p
  separated : Separated p 2
  twoSidedContacts : ∀ i, ‖p i‖ < b → p i ≠ 0 →
    (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      0 < planeCross (p i) (p j - p i)) ∧
    (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      planeCross (p i) (p j - p i) < 0)
  innerCap : ∀ i, ‖p i‖ < b → ‖p i‖ < D b
  strictBlocker : ∀ i, ‖p i‖ < b → p i ≠ 0 →
    ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ
  coreCap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b
  coreCapSmall : F b < Real.sqrt 2
  coreCount : (nonOuterIndices p b).card ≤ 2
  boundaryCount : (boundarySet p b).card ≤ 10
  touchingCount : (touchingInnerSet p b).card ≤ 7
  elementaryLower : 1 + Real.sqrt 5 ≤ b

theorem exists_selectedPacking15 :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane, SelectedPacking15 p b := by
  obtain ⟨b, p, hbB, hopt, hp, hs, hKmax, hSmax, hD, hblock,
    hFcap, hFsmall, _⟩ := exists_optimal_selected_full_maximal
  have hb : 2 < b := centerFeasible_radius_gt_two hopt.1
  have hK := boundary_count_le_ten p b (by linarith) hbB hs
  have htwo : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        0 < planeCross (p i) (p j - p i)) ∧
      (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        planeCross (p i) (p j - p i) < 0) := by
    intro i hi hnz
    exact inner_has_two_sided_contacts_of_maximal p b ⟨hp, hs⟩
      hKmax hSmax i hi hnz
  have hm : (nonOuterIndices p b).card ≤ 2 := by
    by_contra hn
    exact m3_impossible_at_K_le_ten p b hb hbB ⟨hp, hs⟩ hD
      hFcap hFsmall hblock hK (by omega)
  exact ⟨b, p, ⟨hbB, hopt, hp, hs, htwo, hD, hblock,
    hFcap, hFsmall, hm, hK,
    touchingInner_count_le_seven p b hbB ⟨hp, hs⟩ hD,
    centerFeasible_radius_ge_one_add_sqrt_five hopt.1⟩⟩

/-- These seven rows exhaust the zero- and one-core branch. -/
def SevenResidualRows (K m : ℕ) : Prop :=
  (K = 7 ∧ m = 1) ∨ (K = 8 ∧ m = 0) ∨ (K = 8 ∧ m = 1) ∨
  (K = 9 ∧ m = 0) ∨ (K = 9 ∧ m = 1) ∨ (K = 10 ∧ m = 0) ∨
  (K = 10 ∧ m = 1)

theorem SelectedPacking15.seven_rows {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b)
    (hm : (nonOuterIndices p b).card ≤ 1) :
    SevenResidualRows (boundarySet p b).card (nonOuterIndices p b).card := by
  have hpart := boundary_nonOuter_touching_card_partition p b h.inDisk
  have hK := h.boundaryCount
  have ht := h.touchingCount
  unfold SevenResidualRows
  omega

/-- Actual strict blocker/outer-contact data for two distinct core centers.
The witness is the original packing's index family, not a surrogate model. -/
def DistinctCoreWitness15 (p : Fin 15 → Plane) (b : ℝ) : Prop :=
  ∃ target blocker outer : Fin 2 → Fin 15,
    Function.Injective target ∧
    (∀ c, ‖p (target c)‖ < b ∧ ¬TouchesOuter p b (target c)) ∧
    (∀ c, blocker c ≠ target c ∧
      dist (p (target c)) (p (blocker c)) = 2 ∧
      ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
      outer c ≠ blocker c ∧ ‖p (outer c)‖ = b ∧
      dist (p (blocker c)) (p (outer c)) = 2 ∧
      ‖p (target c)‖ ^ 2 < ⟪p (blocker c), p (target c)⟫_ℝ) ∧
    blocker 0 ≠ blocker 1

/-- The shared-blocker exclusion and the correlated-radius certificate
are connected here to the same selected representative. -/
theorem SelectedPacking15.two_core_distinct {p : Fin 15 → Plane} {b : ℝ}
    (h : SelectedPacking15 p b)
    (hm : (nonOuterIndices p b).card = 2) :
    (boundarySet p b).card = 9 ∧ (7 / 2 : ℝ) < b ∧
      DistinctCoreWitness15 p b := by
  have hb : 2 < b := centerFeasible_radius_gt_two h.optimal.1
  have hpack : InDisk b p ∧ Separated p 2 := ⟨h.inDisk, h.separated⟩
  have hK9 := m2_requires_K9 p b hb h.belowCandidate hpack h.innerCap
    h.coreCap h.coreCapSmall h.strictBlocker hm.ge h.coreCount
  obtain ⟨target, blocker, outer, htarget, hno, hdata, hsplit⟩ :=
    m2_K9_shared_or_distinct_budget p b hb h.belowCandidate hpack
      h.innerCap h.coreCap h.coreCapSmall h.strictBlocker hK9 hm.ge
  rcases hsplit with ⟨hsame, hsq, hbcut⟩ | ⟨hne, _⟩
  · exact False.elim (m2_K9_shared_impossible p b hb h.belowCandidate
      hpack h.innerCap h.coreCap hK9 hm target blocker outer
      htarget hno hdata hsame hsq hbcut)
  · have hhalf := distinct_m2_K9_requires_b_gt_seven_halves p b hb
      h.belowCandidate hpack h.innerCap h.coreCap h.coreCapSmall
      h.strictBlocker hK9 hm target blocker outer htarget hno hdata hne
    exact ⟨hK9, hhalf, target, blocker, outer, htarget, hno, hdata, hne⟩

/-- Unconditional current frontier, starting from the original fifteen-point
problem. The residual branches are stated explicitly and remain obligations;
this is not a theorem that the candidate is globally optimal. -/
theorem exists_selectedPacking15_at_formal_frontier :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane, SelectedPacking15 p b ∧
      (SevenResidualRows (boundarySet p b).card (nonOuterIndices p b).card ∨
        ((nonOuterIndices p b).card = 2 ∧ (boundarySet p b).card = 9 ∧
          (7 / 2 : ℝ) < b ∧ DistinctCoreWitness15 p b)) := by
  obtain ⟨b, p, h⟩ := exists_selectedPacking15
  refine ⟨b, p, h, ?_⟩
  by_cases hm1 : (nonOuterIndices p b).card ≤ 1
  · exact Or.inl (h.seven_rows hm1)
  · have hm2 : (nonOuterIndices p b).card = 2 := by
      have := h.coreCount
      omega
    exact Or.inr ⟨hm2, h.two_core_distinct hm2⟩

end CP15
