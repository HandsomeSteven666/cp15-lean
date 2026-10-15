import CP15.UniqueExtensionSymmetry
import CP15.K10ActualGapEquality

open scoped InnerProductSpace

namespace CP15

/-- A feasible labelled packing, kept as a subtype so that every edge in the
component ascent graph has feasible endpoints. -/
def FeasiblePacking15 (b : ℝ) := {p : Fin 15 → Plane // p ∈ FeasibleSet15 b}

noncomputable def componentMaxRepresentative (b : ℝ)
    (p : FeasiblePacking15 b) : Fin 15 → Plane :=
  Classical.choose (exists_max_boundary_in_component p.1 b p.2)

theorem componentMaxRepresentative_spec (b : ℝ)
    (p : FeasiblePacking15 b) :
    componentMaxRepresentative b p ∈
        connectedComponentIn (FeasibleSet15 b) p.1 ∧
      ∀ r, r ∈ connectedComponentIn (FeasibleSet15 b) p.1 →
        (boundarySet r b).card ≤
          (boundarySet (componentMaxRepresentative b p) b).card :=
  Classical.choose_spec (exists_max_boundary_in_component p.1 b p.2)

noncomputable def componentRank (b : ℝ) (p : FeasiblePacking15 b) : ℕ :=
  (boundarySet (componentMaxRepresentative b p) b).card

theorem componentRank_max (b : ℝ) (p : FeasiblePacking15 b)
    (r : Fin 15 → Plane)
    (hr : r ∈ connectedComponentIn (FeasibleSet15 b) p.1) :
    (boundarySet r b).card ≤ componentRank b p :=
  (componentMaxRepresentative_spec b p).2 r hr

theorem componentRank_le_ten (b : ℝ) (hb : 0 < b)
    (hbB : b ≤ candidateB) (p : FeasiblePacking15 b) :
    componentRank b p ≤ 10 := by
  have hr := (connectedComponentIn_subset (FeasibleSet15 b) p.1)
    (componentMaxRepresentative_spec b p).1
  exact boundary_count_le_ten (componentMaxRepresentative b p) b
    hb hbB hr.2

/-- A single center of a maximum-boundary-count packing in the source
component is replaced by a boundary center. The target is supplied with a
proof of feasibility; it may belong to a different component. -/
def ComponentBoundaryStep (b : ℝ)
    (p q : FeasiblePacking15 b) : Prop :=
  ∃ r : Fin 15 → Plane, ∃ i : Fin 15, ∃ x : Plane,
    r ∈ connectedComponentIn (FeasibleSet15 b) p.1 ∧
    (boundarySet r b).card = componentRank b p ∧
    ‖r i‖ < b ∧ ‖x‖ = b ∧ q.1 = Function.update r i x

theorem boundarySet_update_inner_to_boundary
    (r : Fin 15 → Plane) (b : ℝ) (i : Fin 15) (x : Plane)
    (_hi : ‖r i‖ < b) (hx : ‖x‖ = b) :
    boundarySet (Function.update r i x) b =
      insert i (boundarySet r b) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [boundarySet, hx]
  · simp [boundarySet, hji]

theorem componentBoundaryStep_rank_increase (b : ℝ)
    (p q : FeasiblePacking15 b)
    (hstep : ComponentBoundaryStep b p q) :
    componentRank b p < componentRank b q := by
  obtain ⟨r, i, x, hr, hK, hi, hx, hq⟩ := hstep
  have hnot : i ∉ boundarySet r b := by
    simp [boundarySet, ne_of_lt hi]
  have hcard : (boundarySet q.1 b).card =
      (boundarySet r b).card + 1 := by
    rw [hq, boundarySet_update_inner_to_boundary r b i x hi hx]
    simp [hnot]
  have hqmem : q.1 ∈ connectedComponentIn (FeasibleSet15 b) q.1 :=
    mem_connectedComponentIn q.2
  have hle := componentRank_max b q q.1 hqmem
  omega

/-- The terminal graph condition is exactly the absence of any feasible
one-center boundary replacement from a maximum-count representative in the
component. -/
theorem terminal_component_noBoundaryReplacement (b : ℝ)
    (p : FeasiblePacking15 b)
    (hterminal : ¬∃ q : FeasiblePacking15 b,
      ComponentBoundaryStep b p q)
    (r : Fin 15 → Plane)
    (hr : r ∈ connectedComponentIn (FeasibleSet15 b) p.1)
    (hK : (boundarySet r b).card = componentRank b p) :
    NoBoundaryReplacement r b := by
  intro i x hi hx hfeas
  let q : FeasiblePacking15 b :=
    ⟨Function.update r i x, hfeas⟩
  apply hterminal
  exact ⟨q, r, i, x, hr, hK, hi, hx, rfl⟩

/-- The geometric inner-radius cap is available at every terminal vertex
of the actual replacement graph, after the two component-local tie-breaks. -/
theorem terminal_component_selected_with_cap (b : ℝ) (hb : 2 < b)
    (p : FeasiblePacking15 b)
    (hterminal : ¬∃ q : FeasiblePacking15 b,
      ComponentBoundaryStep b p q) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 b) p.1 ∧
      MaxSumInComponent q b ∧
      (∀ i, ‖q i‖ < b → ‖q i‖ < D b) := by
  apply exists_terminal_component_selected_with_cap p.1 b p.2 hb
  intro q hq hK
  apply terminal_component_noBoundaryReplacement b p hterminal q hq
  apply le_antisymm
  · exact componentRank_max b p q hq
  · exact hK (componentMaxRepresentative b p)
      (componentMaxRepresentative_spec b p).1

/-- Every terminal component at the optimal radius contains a representative
with all geometric fields required by the existing exclusion chain. The
two-sided contact field is supplied by component-local maximality. -/
theorem terminal_component_selectedPacking15
    (p : FeasiblePacking15 candidateB)
    (hterminal : ¬∃ q : FeasiblePacking15 candidateB,
      ComponentBoundaryStep candidateB p q) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 ∧
      SelectedPacking15 q candidateB := by
  have hb : 2 < candidateB :=
    centerFeasible_radius_gt_two centerOptimal_candidate.1
  obtain ⟨q, hq, hmax, hD⟩ :=
    terminal_component_selected_with_cap candidateB hb p hterminal
  have hpack : InDisk candidateB q ∧ Separated q 2 :=
    (connectedComponentIn_subset (FeasibleSet15 candidateB) p.1) hq
  have hblock : ∀ i, ‖q i‖ < candidateB → q i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (q i) (q j) = 2 ∧
        ‖q i‖ ^ 2 < ⟪q j, q i⟫_ℝ := by
    intro i hi hnz
    exact strict_radial_blocker_of_component_maxSum q candidateB
      hpack hmax i hi hnz
  have htwo : ∀ i, ‖q i‖ < candidateB → q i ≠ 0 →
      (∃ j, j ≠ i ∧ dist (q i) (q j) = 2 ∧
        0 < planeCross (q i) (q j - q i)) ∧
      (∃ j, j ≠ i ∧ dist (q i) (q j) = 2 ∧
        planeCross (q i) (q j - q i) < 0) := by
    intro i hi hnz
    exact two_sided_contacts_of_component_maxSum q candidateB
      hpack hmax i hi hnz
  have hFcap : ∀ i, ‖q i‖ < candidateB →
      ¬TouchesOuter q candidateB i → ‖q i‖ ≤ F candidateB := by
    intro i hi hno
    exact nonouter_F_cap q candidateB hb hpack hD hblock i hi hno
  have hFsmall : F candidateB < Real.sqrt 2 :=
    Candidate.F_lt_sqrt_two_of_le_candidateB hb (le_refl _)
  have hK : (boundarySet q candidateB).card ≤ 10 :=
    boundary_count_le_ten q candidateB (by linarith) (le_refl _) hpack.2
  have hm : (nonOuterIndices q candidateB).card ≤ 2 := by
    by_contra hn
    exact m3_impossible_at_K_le_ten q candidateB hb (le_refl _)
      hpack hD hFcap hFsmall hblock hK (by omega)
  refine ⟨q, hq, ?_⟩
  exact ⟨le_refl _, centerOptimal_candidate, hpack.1, hpack.2,
    htwo, hD, hblock, hFcap, hFsmall, hm, hK,
    touchingInner_count_le_seven q candidateB (le_refl _) hpack hD,
    centerFeasible_radius_ge_one_add_sqrt_five
      centerOptimal_candidate.1⟩

theorem terminal_component_K10m0
    (p : FeasiblePacking15 candidateB)
    (hterminal : ¬∃ q : FeasiblePacking15 candidateB,
      ComponentBoundaryStep candidateB p q) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 ∧
      (boundarySet q candidateB).card = 10 ∧
      (nonOuterIndices q candidateB).card = 0 := by
  obtain ⟨q, hq, hselected⟩ :=
    terminal_component_selectedPacking15 p hterminal
  exact ⟨q, hq, hselected.only_K10m0⟩

/-- The existing exact equality certificate also applies to the actual
representative of every terminal component. This classifies its scalar
cyclic model; identifying its labelled coordinates requires a further
geometry theorem. -/
theorem terminal_component_scalar_equality
    (p : FeasiblePacking15 candidateB)
    (hterminal : ¬∃ q : FeasiblePacking15 candidateB,
      ComponentBoundaryStep candidateB p q) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 ∧
      ∃ r : Fin 5 → ℝ, ∃ empty : Fin 5 → ℕ, ∃ g : Fin 5 → ℝ,
        CyclicInnerModel candidateB r empty g ∧
        (∀ i, empty i = 1) ∧
        (∀ i, r i = candidateInnerRadius) ∧
        (∀ i, g i = 2 * Real.pi / 5) := by
  obtain ⟨q, hq, hselected⟩ :=
    terminal_component_selectedPacking15 p hterminal
  obtain ⟨hK, hm⟩ := hselected.only_K10m0
  obtain ⟨r, empty, g, hmodel, _, he, hr, hg⟩ :=
    hselected.K10m0_scalar_equality hK hm
  exact ⟨q, hq, r, empty, g, hmodel, he, hr, hg⟩

/-- The equality data now refer to five actual indices of the terminal
component's selected packing, rather than anonymous scalar witnesses. -/
theorem terminal_component_actual_inner_equalities
    (p : FeasiblePacking15 candidateB)
    (hterminal : ¬∃ q : FeasiblePacking15 candidateB,
      ComponentBoundaryStep candidateB p q) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 ∧
      ∃ ix : Fin 5 → Fin 15, ∃ u : Fin 5 → Fin 10,
        ∃ φ : Fin 5 → ℝ,
          Function.Injective ix ∧ StrictMono u ∧
          (∀ i, ‖q (ix i)‖ = candidateInnerRadius) ∧
          (∀ i, occupiedEmptyCount u i = 1) ∧
          (∀ i, cyclicAngleGap φ i = 2 * Real.pi / 5) := by
  obtain ⟨q, hq, hselected⟩ :=
    terminal_component_selectedPacking15 p hterminal
  obtain ⟨hK, hm⟩ := hselected.only_K10m0
  obtain ⟨ix, u, φ, _, hix, hu, _, hr, he, hg, _, _, _, _, _, _⟩ :=
    hselected.K10m0_actual_inner_equalities hK hm
  exact ⟨q, hq, ix, u, φ, hix, hu, hr, he, hg⟩

/-- All fifteen centers of a terminal representative are now accounted for
by the equality data: the five inner centers exhaust the nonboundary
indices, while the ten ordered outer centers exhaust the boundary indices. -/
theorem terminal_component_actual_angular_equalities
    (p : FeasiblePacking15 candidateB)
    (hterminal : ¬∃ q : FeasiblePacking15 candidateB,
      ComponentBoundaryStep candidateB p q) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 ∧
      ∃ ix : Fin 5 → Fin 15, ∃ o : Fin 10 → Fin 15,
        ∃ u : Fin 5 → Fin 10, ∃ φ : Fin 5 → ℝ,
          Function.Injective ix ∧ Function.Injective o ∧
          (∃ a : Fin 2, ∀ i,
            (u i).val = a.val + 2 * i.val) ∧
          (∀ i, ‖q (ix i)‖ = candidateInnerRadius) ∧
          (∀ k, ‖q (o k)‖ = candidateB) ∧
          (∀ j, ‖q j‖ = candidateB → ∃ k, o k = j) ∧
          (∀ j, ‖q j‖ < candidateB → ∃ i, ix i = j) ∧
          (∀ i, φ i = polarArg (q (ix i)) ∨
            φ i = polarArg (q (ix i)) + 2 * Real.pi) ∧
          (∀ i, cyclicAngleGap φ i = 2 * Real.pi / 5) ∧
          (∀ k, (∀ i, u i ≠ k) →
            cyclicAngleGap (fun j => polarArg (q (o j))) k =
              outerAlpha candidateB) ∧
          (∀ i, cyclicAngleGap (fun j => polarArg (q (o j))) (u i) =
            2 * contactAngle candidateB candidateInnerRadius) ∧
          (∀ i, φ i = polarArg (q (o (u i))) +
            contactAngle candidateB candidateInnerRadius) := by
  obtain ⟨q, hq, hselected⟩ :=
    terminal_component_selectedPacking15 p hterminal
  obtain ⟨hK, hm⟩ := hselected.only_K10m0
  obtain ⟨ix, u, φ, ψ, hix, _, halternating, hinner, hr, hlift,
    hφgap, hoccupied, hempty, hphase, hψmono, hψmem⟩ :=
    hselected.K10m0_actual_gap_equalities hK hm
  obtain ⟨o, ho, houter, houterComplete⟩ :=
    actual_boundary_order_of_gap_data q candidateB hK ψ hψmono hψmem
  have hψeq : (fun j => polarArg (q (o j))) = ψ := by
    funext j
    exact (houter j).2
  have hcomplete := actual_inner_indices_complete q candidateB hK ix hix hinner
  refine ⟨q, hq, ix, o, u, φ, hix, ho, halternating, hr,
    (fun k => (houter k).1),
    (fun j hj => (houterComplete j hj)), hcomplete, hlift, hφgap,
    ?_, ?_, ?_⟩
  · simpa [hψeq] using hempty
  · simpa [hψeq] using hoccupied
  · intro i
    simpa [(houter (u i)).2] using hphase i

/-- This instantiates the abstract bounded ascent theorem with the actual
packing space and the actual one-point replacement relation. The sole
remaining hypothesis is a theorem about terminal components. -/
theorem all_feasible_packings_unique_extensions_of_terminal
    (b : ℝ) (hb : 0 < b) (hbB : b ≤ candidateB)
    (hterminalUnique :
      ∀ p : FeasiblePacking15 b,
        (∀ r, r ∈ connectedComponentIn (FeasibleSet15 b) p.1 →
          (boundarySet r b).card = componentRank b p →
            NoBoundaryReplacement r b) →
        ∀ r, r ∈ connectedComponentIn (FeasibleSet15 b) p.1 →
          UniqueOnePointExtension r b) :
    ∀ p : FeasiblePacking15 b, UniqueOnePointExtension p.1 b := by
  let Good : FeasiblePacking15 b → Prop := fun p =>
    ∀ r, r ∈ connectedComponentIn (FeasibleSet15 b) p.1 →
      UniqueOnePointExtension r b
  have hgood := all_good_of_bounded_ascent
    (componentRank b) 10 (ComponentBoundaryStep b) Good
    (componentRank_le_ten b hb hbB)
    (componentBoundaryStep_rank_increase b)
    (by
      intro p hnone
      exact hterminalUnique p
        (terminal_component_noBoundaryReplacement b p hnone))
    (by
      intro p q hstep hqgood
      obtain ⟨r, i, x, hr, hK, hi, hx, hq⟩ := hstep
      have hrfeas : r ∈ FeasibleSet15 b :=
        (connectedComponentIn_subset (FeasibleSet15 b) p.1) hr
      have hqunique : UniqueOnePointExtension q.1 b :=
        hqgood q.1 (mem_connectedComponentIn q.2)
      have hstrict : (boundarySet r b).card <
          (boundarySet q.1 b).card := by
        rw [hq, boundarySet_update_inner_to_boundary r b i x hi hx]
        have hnot : i ∉ boundarySet r b := by
          simp [boundarySet, ne_of_lt hi]
        simp [hnot]
      exact no_boundary_increase_into_unique r q.1 b i x
        hrfeas hq hqunique hstrict)
  intro p
  exact hgood p p.1 (mem_connectedComponentIn p.2)

/-- The fully instantiated global-uniqueness implication. Only two
candidate-specific geometric statements remain as explicit premises:
the terminal-component classification and the one-point extension theorem.
Neither is postulated as an axiom. -/
theorem all_optimal_packings_congruent_of_terminal_and_extension
    (hterminalCongruent :
      ∀ p : FeasiblePacking15 candidateB,
        (¬∃ q : FeasiblePacking15 candidateB,
          ComponentBoundaryStep candidateB p q) →
        ∀ r, r ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 →
          CenteredCongruent15 r Candidate.pointAtSeparationTwo)
    (hunique : UniqueBoundaryPointFromOthers
      Candidate.pointAtSeparationTwo candidateB) :
    ∀ p : FeasiblePacking15 candidateB,
      CenteredCongruent15 p.1 Candidate.pointAtSeparationTwo := by
  let Good : FeasiblePacking15 candidateB → Prop := fun p =>
    ∀ r, r ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 →
      CenteredCongruent15 r Candidate.pointAtSeparationTwo
  have hb : 0 < candidateB := candidateB_pos
  have hgood := all_good_of_bounded_ascent
    (componentRank candidateB) 10
    (ComponentBoundaryStep candidateB) Good
    (componentRank_le_ten candidateB hb (le_refl _))
    (componentBoundaryStep_rank_increase candidateB)
    (by
      intro p hnone
      exact hterminalCongruent p hnone)
    (by
      intro p q hstep hqgood
      obtain ⟨r, i, x, hr, hK, hi, hx, hq⟩ := hstep
      have hrfeas : r ∈ FeasibleSet15 candidateB :=
        (connectedComponentIn_subset (FeasibleSet15 candidateB) p.1) hr
      have hqcong : CenteredCongruent15 q.1
          Candidate.pointAtSeparationTwo :=
        hqgood q.1 (mem_connectedComponentIn q.2)
      have hqunique : UniqueBoundaryPointFromOthers q.1 candidateB :=
        uniqueBoundaryPointFromOthers_of_centeredCongruent
          q.1 Candidate.pointAtSeparationTwo candidateB hqcong hunique
      have hstrict : (boundarySet r candidateB).card <
          (boundarySet q.1 candidateB).card := by
        rw [hq, boundarySet_update_inner_to_boundary r candidateB i x hi hx]
        have hnot : i ∉ boundarySet r candidateB := by
          simp [boundarySet, ne_of_lt hi]
        simp [hnot]
      exact no_boundary_increase_into_unique_boundary r q.1 candidateB i x
        hrfeas hi hx hq hqunique hstrict)
  intro p
  exact hgood p p.1 (mem_connectedComponentIn p.2)

/-- Splitting the terminal premise into its two independent geometric
obligations: identify one selected representative, then prove rigidity of
the candidate's whole connected component. -/
theorem all_optimal_packings_congruent_of_rep_rigidity_and_extension
    (hterminalRepresentative :
      ∀ p : FeasiblePacking15 candidateB,
        (¬∃ q : FeasiblePacking15 candidateB,
          ComponentBoundaryStep candidateB p q) →
        ∃ r, r ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 ∧
          CenteredCongruent15 r Candidate.pointAtSeparationTwo)
    (hcandidateComponentRigidity :
      ∀ q : FeasiblePacking15 candidateB,
        CenteredCongruent15 q.1 Candidate.pointAtSeparationTwo →
        ∀ r, r ∈ connectedComponentIn (FeasibleSet15 candidateB) q.1 →
          CenteredCongruent15 r Candidate.pointAtSeparationTwo)
    (hunique : UniqueBoundaryPointFromOthers
      Candidate.pointAtSeparationTwo candidateB) :
    ∀ p : FeasiblePacking15 candidateB,
      CenteredCongruent15 p.1 Candidate.pointAtSeparationTwo := by
  apply all_optimal_packings_congruent_of_terminal_and_extension
  · intro p hterminal r hr
    obtain ⟨q, hq, hqcong⟩ := hterminalRepresentative p hterminal
    have hqfeas : q ∈ FeasibleSet15 candidateB :=
      (connectedComponentIn_subset (FeasibleSet15 candidateB) p.1) hq
    have hrq : r ∈ connectedComponentIn (FeasibleSet15 candidateB) q := by
      rw [← connectedComponentIn_eq hq]
      exact hr
    exact hcandidateComponentRigidity ⟨q, hqfeas⟩ hqcong r hrq
  · exact hunique

end CP15
