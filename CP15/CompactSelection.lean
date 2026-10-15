import CP15.Blocker
import CP15.Selection

open scoped InnerProductSpace

namespace CP15

def FeasibleWithBoundary {n : ℕ} (b : ℝ) (S : Finset (Fin n)) :
    Set (Fin n → Plane) :=
  {p | InDisk b p ∧ Separated p 2 ∧ ∀ i ∈ S, ‖p i‖ = b}

theorem isCompact_inDisk {n : ℕ} (b : ℝ) :
    IsCompact {p : Fin n → Plane | InDisk b p} := by
  have hball : ∀ i : Fin n, IsCompact (Metric.closedBall (0 : Plane) b) :=
    fun _ => isCompact_closedBall 0 b
  have hprod := isCompact_pi_infinite hball
  convert hprod using 1
  ext p
  simp [InDisk, Metric.mem_closedBall, dist_zero_right]

theorem isClosed_separated {n : ℕ} :
    IsClosed {p : Fin n → Plane | Separated p 2} := by
  have hpair (i j : Fin n) :
      IsClosed {p : Fin n → Plane | i ≠ j → 2 ≤ dist (p i) (p j)} := by
    by_cases hij : i = j
    · subst j
      simp
    · simpa [hij] using
        (isClosed_le continuous_const
          ((continuous_apply i).dist (continuous_apply j)))
  have hall : IsClosed
      (⋂ i : Fin n, ⋂ j : Fin n,
        {p : Fin n → Plane | i ≠ j → 2 ≤ dist (p i) (p j)}) :=
    isClosed_iInter (fun i => isClosed_iInter (fun j => hpair i j))
  convert hall using 1
  ext p
  simp [Separated]

theorem isClosed_boundary_equalities {n : ℕ} (b : ℝ)
    (S : Finset (Fin n)) :
    IsClosed {p : Fin n → Plane | ∀ i ∈ S, ‖p i‖ = b} := by
  have hall : IsClosed
      (⋂ i ∈ S, {p : Fin n → Plane | ‖p i‖ = b}) := by
    apply isClosed_biInter
    intro i hi
    exact isClosed_eq ((continuous_apply i).norm) continuous_const
  convert hall using 1
  ext p
  simp

theorem isCompact_feasibleWithBoundary {n : ℕ} (b : ℝ)
    (S : Finset (Fin n)) :
    IsCompact (FeasibleWithBoundary b S) := by
  have hclosed : IsClosed (FeasibleWithBoundary b S) := by
    have hclosedBase : IsClosed ({p | InDisk b p} ∩
      {p | Separated p 2} ∩
      {p | ∀ i ∈ S, ‖p i‖ = b}) :=
        ((isCompact_inDisk b).isClosed.inter isClosed_separated).inter
          (isClosed_boundary_equalities b S)
    convert hclosedBase using 1
    ext p
    simp [FeasibleWithBoundary, and_assoc]
  apply (isCompact_inDisk b).of_isClosed_subset hclosed
  intro p hp
  exact hp.1

theorem radiusSum_continuous {n : ℕ} :
    Continuous (radiusSum : (Fin n → Plane) → ℝ) := by
  unfold radiusSum
  apply continuous_finsetSum
  intro i hi
  exact (continuous_apply i).norm

/-- Selects one boundary pattern of maximum size, then maximizes the norm
sum within that closed pattern. This supplies the compatible tie-break. -/
theorem exists_maxBoundary_maxSum {n : ℕ} {b : ℝ}
    (h : CenterFeasible n b) :
    ∃ p : Fin n → Plane,
      InDisk b p ∧ Separated p 2 ∧
        MaxBoundaryCount p b ∧ MaxSumAtBoundaryCount p b := by
  obtain ⟨p, hp, hs, hK⟩ := exists_maxBoundaryCount h
  let S := boundarySet p b
  have hpS : p ∈ FeasibleWithBoundary b S := by
    refine ⟨hp, hs, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hnonempty : (FeasibleWithBoundary b S).Nonempty := ⟨p, hpS⟩
  obtain ⟨q, hqS, hqmax⟩ :=
    (isCompact_feasibleWithBoundary b S).exists_isMaxOn
      hnonempty radiusSum_continuous.continuousOn
  have hsubset : S ⊆ boundarySet q b := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqS.2.2 i hi⟩
  have hcardle : (boundarySet q b).card ≤ S.card := hK q hqS.1 hqS.2.1
  have hqboundary : boundarySet q b = S :=
    (Finset.eq_of_subset_of_card_le hsubset hcardle).symm
  refine ⟨q, hqS.1, hqS.2.1, ?_, ?_⟩
  · intro z hz hzs
    simpa [hqboundary] using hK z hz hzs
  · intro z hz hzs hzboundary
    have hzS : z ∈ FeasibleWithBoundary b S := by
      refine ⟨hz, hzs, ?_⟩
      intro i hi
      have hiz : i ∈ boundarySet z b := by
        rw [hzboundary, hqboundary]
        exact hi
      exact (Finset.mem_filter.mp hiz).2
    exact hqmax hzS

theorem exists_selected_inner_cap_and_blocker {n : ℕ} {b : ℝ}
    (hb : 2 < b) (h : CenterFeasible n b) :
    ∃ p : Fin n → Plane,
      InDisk b p ∧ Separated p 2 ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → p i ≠ 0 →
        ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
          ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ) := by
  obtain ⟨p, hp, hs, hK, hS⟩ := exists_maxBoundary_maxSum h
  refine ⟨p, hp, hs, ?_, ?_⟩
  · exact inner_cap_of_noBoundaryReplacement p b hb ⟨hp, hs⟩
      (noBoundaryReplacement_of_maxBoundaryCount p b hK)
  · intro i hi hnz
    exact strict_radial_blocker_of_no_outward_move p b i ⟨hp, hs⟩ hi hnz
      (noFeasibleOutwardMove_of_maximal p b hK hS)

/-- The same selection package, retaining both tie-break premises for
later tangential perturbations. No second representative is chosen. -/
theorem exists_selected_inner_cap_blocker_maximal {n : ℕ} {b : ℝ}
    (hb : 2 < b) (h : CenterFeasible n b) :
    ∃ p : Fin n → Plane,
      InDisk b p ∧ Separated p 2 ∧
      MaxBoundaryCount p b ∧ MaxSumAtBoundaryCount p b ∧
      (∀ i, ‖p i‖ < b → ‖p i‖ < D b) ∧
      (∀ i, ‖p i‖ < b → p i ≠ 0 →
        ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
          ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ) := by
  obtain ⟨p, hp, hs, hK, hS⟩ := exists_maxBoundary_maxSum h
  refine ⟨p, hp, hs, hK, hS, ?_, ?_⟩
  · exact inner_cap_of_noBoundaryReplacement p b hb ⟨hp, hs⟩
      (noBoundaryReplacement_of_maxBoundaryCount p b hK)
  · intro i hi hnz
    exact strict_radial_blocker_of_no_outward_move p b i ⟨hp, hs⟩ hi hnz
      (noFeasibleOutwardMove_of_maximal p b hK hS)

end CP15
