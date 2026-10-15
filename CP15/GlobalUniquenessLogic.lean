import CP15.GlobalEndpoint

open scoped InnerProductSpace Topology

namespace CP15

/-- The precise one-point extension property needed to rule out an
incoming boundary replacement at a candidate configuration. -/
def UniqueOnePointExtension (q : Fin 15 → Plane) (b : ℝ) : Prop :=
  ∀ i x, InDisk b (Function.update q i x) →
    Separated (Function.update q i x) 2 → x = q i

/-- This is the direct geometric statement certified by the two
deletion-orbit calculations. It does not assume that the other fourteen
points form a feasible packing. -/
def UniquePointFromOthers (q : Fin 15 → Plane) (b : ℝ) : Prop :=
  ∀ i x, ‖x‖ ≤ b →
    (∀ j, j ≠ i → 2 ≤ dist x (q j)) → x = q i

/-- The global ascent argument only deletes a boundary center from the
target of an incoming replacement. No assertion about deleting an inner
candidate center is required. -/
def UniqueBoundaryPointFromOthers (q : Fin 15 → Plane) (b : ℝ) : Prop :=
  ∀ i, ‖q i‖ = b → ∀ x, ‖x‖ ≤ b →
    (∀ j, j ≠ i → 2 ≤ dist x (q j)) → x = q i

theorem uniqueBoundaryPointFromOthers_of_uniquePointFromOthers
    (q : Fin 15 → Plane) (b : ℝ)
    (h : UniquePointFromOthers q b) :
    UniqueBoundaryPointFromOthers q b := by
  intro i _ x hx hs
  exact h i x hx hs

theorem uniqueOnePointExtension_of_uniquePointFromOthers
    (q : Fin 15 → Plane) (b : ℝ)
    (h : UniquePointFromOthers q b) :
    UniqueOnePointExtension q b := by
  intro i x hd hs
  apply h i x
  · simpa using hd i
  · intro j hji
    have hsep := hs i j (Ne.symm hji)
    simpa [Function.update_of_ne hji] using hsep

/-- A feasible packing cannot differ in one position from a packing with
unique one-point extensions. This statement is independent of labels,
coordinates, or any graph argument. -/
theorem eq_of_one_point_replacement_into_unique
    (p q : Fin 15 → Plane) (b : ℝ) (i : Fin 15) (x : Plane)
    (hp : InDisk b p ∧ Separated p 2)
    (hq : q = Function.update p i x)
    (hu : UniqueOnePointExtension q b) : p = q := by
  have hback : Function.update q i (p i) = p := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hq, hji]
  have hi : p i = q i := by
    apply hu i (p i)
    · rw [hback]
      exact hp.1
    · rw [hback]
      exact hp.2
  funext j
  by_cases hji : j = i
  · subst j
    exact hi
  · simp [hq, hji]

/-- A unique-extension packing has no incoming one-point replacement
that strictly increases the number of boundary centers. -/
theorem no_boundary_increase_into_unique
    (p q : Fin 15 → Plane) (b : ℝ) (i : Fin 15) (x : Plane)
    (hp : InDisk b p ∧ Separated p 2)
    (hq : q = Function.update p i x)
    (hu : UniqueOnePointExtension q b)
    (hinc : (boundarySet p b).card < (boundarySet q b).card) : False := by
  have heq := eq_of_one_point_replacement_into_unique p q b i x hp hq hu
  rw [heq] at hinc
  exact (lt_irrefl _) hinc

theorem no_boundary_increase_into_unique_boundary
    (p q : Fin 15 → Plane) (b : ℝ) (i : Fin 15) (x : Plane)
    (hp : InDisk b p ∧ Separated p 2)
    (_hi : ‖p i‖ < b) (hx : ‖x‖ = b)
    (hq : q = Function.update p i x)
    (hu : UniqueBoundaryPointFromOthers q b)
    (hinc : (boundarySet p b).card < (boundarySet q b).card) : False := by
  have hqi : ‖q i‖ = b := by simpa [hq] using hx
  have hback : p i = q i := by
    apply hu i hqi (p i) (hp.1 i)
    intro j hji
    have hsep := hp.2 i j (Ne.symm hji)
    simpa [hq, Function.update_of_ne hji] using hsep
  have hpq : p = q := by
    funext j
    by_cases hji : j = i
    · subst j
      exact hback
    · simp [hq, hji]
  rw [hpq] at hinc
  exact (lt_irrefl _) hinc

/-- The exact candidate-specific interface left by the finite geometry
certificate. Once `UniquePointFromOthers` is proved for the candidate,
every putative incoming boundary replacement is ruled out. -/
theorem no_boundary_increase_into_candidate_of_extension
    (hunique : UniquePointFromOthers
      Candidate.pointAtSeparationTwo candidateB)
    (p : Fin 15 → Plane) (i : Fin 15) (x : Plane)
    (hp : InDisk candidateB p ∧ Separated p 2)
    (hq : Candidate.pointAtSeparationTwo = Function.update p i x)
    (hinc : (boundarySet p candidateB).card <
      (boundarySet Candidate.pointAtSeparationTwo candidateB).card) : False := by
  exact no_boundary_increase_into_unique p Candidate.pointAtSeparationTwo
    candidateB i x hp hq
    (uniqueOnePointExtension_of_uniquePointFromOthers _ _ hunique) hinc

/-- Abstract finite ascent argument. The eventual terminal case is good;
strict rank increase and absence of incoming edges to good vertices force
every vertex to be good. No finiteness assumption on the vertex type is
needed. -/
theorem all_good_of_bounded_ascent
    {C : Type*} (rank : C → ℕ) (bound : ℕ)
    (step : C → C → Prop) (Good : C → Prop)
    (hrank : ∀ c, rank c ≤ bound)
    (hincrease : ∀ c d, step c d → rank c < rank d)
    (hterminal : ∀ c, (¬∃ d, step c d) → Good c)
    (hnoIncoming : ∀ c d, step c d → Good d → False) :
    ∀ c, Good c := by
  have hmain : ∀ n : ℕ, ∀ c : C, bound - rank c = n → Good c := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc
      by_cases hout : ∃ d, step c d
      · obtain ⟨d, hstep⟩ := hout
        have hdlt : bound - rank d < n := by
          have hcBound := hrank c
          have hdBound := hrank d
          have hinc := hincrease c d hstep
          omega
        have hdgood := ih (bound - rank d) hdlt d rfl
        exact False.elim (hnoIncoming c d hstep hdgood)
      · exact hterminal c hout
  intro c
  exact hmain (bound - rank c) c rfl

/-- A feasible line segment cannot change connected component. This is the
topological fact used when a small one-center motion contradicts maximality
inside a component. -/
theorem endpoint_mem_connectedComponent_of_segment
    {Y : Type*} [TopologicalSpace Y]
    (f : ℝ → Y) (t : ℝ) (ht : 0 ≤ t)
    (hf : ContinuousOn f (Set.Icc 0 t)) :
    f t ∈ connectedComponent (f 0) := by
  have hconn : IsConnected (f '' Set.Icc 0 t) :=
    (isConnected_Icc ht).image f hf
  have h0 : f 0 ∈ f '' Set.Icc 0 t :=
    Set.mem_image_of_mem f ⟨le_refl _, ht⟩
  have hlast : f t ∈ f '' Set.Icc 0 t :=
    Set.mem_image_of_mem f ⟨ht, le_refl _⟩
  exact hconn.subset_connectedComponent h0 hlast

/-- A right-neighborhood feasibility statement supplies a whole closed
initial segment of feasible parameters, not merely one feasible endpoint. -/
theorem exists_feasible_initial_segment
    (P : ℝ → Prop) (hzero : P 0)
    (hevent : ∀ᶠ s : ℝ in 𝓝[>] 0, P s) :
    ∃ t : ℝ, 0 < t ∧ ∀ s ∈ Set.Icc 0 t, P s := by
  obtain ⟨t, ht, hsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioc_subset).mp hevent
  refine ⟨t, ht, ?_⟩
  intro s hs
  by_cases hsz : s = 0
  · simpa [hsz] using hzero
  · exact hsub ⟨lt_of_le_of_ne hs.1 (Ne.symm hsz), hs.2⟩

/-- The feasible set at a fixed container radius, viewed as a subset of
the ambient labelled configuration space. -/
def FeasibleSet15 (b : ℝ) : Set (Fin 15 → Plane) :=
  {p | InDisk b p ∧ Separated p 2}

theorem feasibleSet15_isClosed (b : ℝ) : IsClosed (FeasibleSet15 b) := by
  have hdisk : IsClosed {p : Fin 15 → Plane | InDisk b p} := by
    have hclosed : IsClosed
        (⋂ i : Fin 15, {p : Fin 15 → Plane | ‖p i‖ ≤ b}) :=
      isClosed_iInter fun i =>
        isClosed_le ((continuous_apply i).norm) continuous_const
    convert hclosed using 1
    ext p
    simp [InDisk]
  have hsep : IsClosed {p : Fin 15 → Plane | Separated p 2} := by
    have hclosed : IsClosed
        (⋂ i : Fin 15, ⋂ j : Fin 15,
          {p : Fin 15 → Plane | i ≠ j → 2 ≤ dist (p i) (p j)}) := by
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j
      by_cases hij : i = j
      · subst j
        simpa using (isClosed_univ : IsClosed (Set.univ : Set (Fin 15 → Plane)))
      · simpa [hij] using
          (isClosed_le continuous_const
            ((continuous_apply i).dist (continuous_apply j)))
    convert hclosed using 1
    ext p
    simp [Separated]
  have hboth := hdisk.inter hsep
  convert hboth using 1
  ext p
  simp [FeasibleSet15]

theorem feasibleSet15_isCompact (b : ℝ) : IsCompact (FeasibleSet15 b) := by
  have hballs : IsCompact
      (Set.pi Set.univ (fun _ : Fin 15 => Metric.closedBall (0 : Plane) b)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  apply IsCompact.of_isClosed_subset hballs (feasibleSet15_isClosed b)
  intro p hp i _
  have hi : ‖p i‖ ≤ b := hp.1 i
  simpa [Metric.mem_closedBall, dist_zero_right] using hi

/-- The component of any feasible packing is compact. This justifies
maximizing the norm sum within a component after fixing its boundary
count. -/
theorem feasible_component_isCompact (p : Fin 15 → Plane) (b : ℝ)
    (hp : p ∈ FeasibleSet15 b) :
    IsCompact (connectedComponentIn (FeasibleSet15 b) p) := by
  letI : CompactSpace (FeasibleSet15 b) :=
    isCompact_iff_compactSpace.mp (feasibleSet15_isCompact b)
  rw [connectedComponentIn_eq_image hp]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

/-- The first tie-break, maximum boundary count, exists separately in
every feasible connected component. It needs only the finite range of
the boundary-count function. -/
theorem exists_max_boundary_in_component
    (p : Fin 15 → Plane) (b : ℝ) (hp : p ∈ FeasibleSet15 b) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 b) p ∧
      ∀ r, r ∈ connectedComponentIn (FeasibleSet15 b) p →
        (boundarySet r b).card ≤ (boundarySet q b).card := by
  let C := connectedComponentIn (FeasibleSet15 b) p
  let K : (Fin 15 → Plane) → ℕ := fun q => (boundarySet q b).card
  have hfinite : (K '' C).Finite := by
    apply (Set.finite_le_nat 15).subset
    rintro k ⟨q, _, rfl⟩
    exact Finset.card_le_card (Finset.subset_univ _)
  have hnonempty : C.Nonempty := ⟨p, mem_connectedComponentIn hp⟩
  obtain ⟨q, hq, hmax⟩ := hfinite.exists_maximalFor' K C hnonempty
  refine ⟨q, hq, ?_⟩
  intro r hr
  rcases le_total (K r) (K q) with hle | hle
  · exact hle
  · exact hmax hr hle

/-- Having at least `k` boundary centers is a closed condition. This is
the compactness input for the second, norm-sum, tie-break. -/
theorem atLeastBoundary_isClosed (b : ℝ) (k : ℕ) :
    IsClosed {p : Fin 15 → Plane | k ≤ (boundarySet p b).card} := by
  classical
  let support (S : Finset (Fin 15)) : Set (Fin 15 → Plane) :=
    {p | ∀ i ∈ S, ‖p i‖ = b}
  have hsupport (S : Finset (Fin 15)) : IsClosed (support S) := by
    have hclosed : IsClosed
        (⋂ i ∈ (S : Set (Fin 15)),
          {p : Fin 15 → Plane | ‖p i‖ = b}) :=
      isClosed_biInter fun i _ =>
        isClosed_eq ((continuous_apply i).norm) continuous_const
    convert hclosed using 1
    ext p
    simp [support]
  have hclosed : IsClosed
      (⋃ S : Finset (Fin 15),
        if k ≤ S.card then support S else ∅) := by
    apply isClosed_iUnion_of_finite
    intro S
    split_ifs <;> simp_all [hsupport]
  convert hclosed using 1
  ext p
  constructor
  · intro hp
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hp ⊢
    refine ⟨boundarySet p b, ?_⟩
    simp only [if_pos hp, Set.mem_setOf_eq, support]
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨S, hS⟩ := hp
    by_cases hk : k ≤ S.card
    · simp only [if_pos hk, Set.mem_setOf_eq, support] at hS
      have hsub : S ⊆ boundarySet p b := by
        intro i hi
        simp [boundarySet, hS i hi]
      exact hk.trans (Finset.card_le_card hsub)
    · simp [hk] at hS

/-- Both tie-break maxima exist in each feasible connected component.
The second maximum is taken on the closed maximum-count stratum. -/
theorem exists_component_selected_packing
    (p : Fin 15 → Plane) (b : ℝ) (hp : p ∈ FeasibleSet15 b) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 b) p ∧
      (∀ r, r ∈ connectedComponentIn (FeasibleSet15 b) p →
        (boundarySet r b).card ≤ (boundarySet q b).card) ∧
      (∀ r, r ∈ connectedComponentIn (FeasibleSet15 b) p →
        (boundarySet r b).card = (boundarySet q b).card →
          radiusSum r ≤ radiusSum q) := by
  let C := connectedComponentIn (FeasibleSet15 b) p
  obtain ⟨q₀, hq₀, hmaxK⟩ := exists_max_boundary_in_component p b hp
  let E : Set (Fin 15 → Plane) :=
    C ∩ {q | (boundarySet q₀ b).card ≤ (boundarySet q b).card}
  have hcompact : IsCompact E :=
    (feasible_component_isCompact p b hp).inter_right
      (atLeastBoundary_isClosed b (boundarySet q₀ b).card)
  have hnonempty : E.Nonempty := by
    refine ⟨q₀, ?_⟩
    change q₀ ∈ C ∧ (boundarySet q₀ b).card ≤ (boundarySet q₀ b).card
    exact ⟨hq₀, le_refl _⟩
  have hcontinuous : Continuous
      (fun q : Fin 15 → Plane => radiusSum q) := by
    unfold radiusSum
    fun_prop
  obtain ⟨q, hqE, hmaxS⟩ :=
    hcompact.exists_isMaxOn hnonempty hcontinuous.continuousOn
  have hqC : q ∈ C := hqE.1
  have hqK : (boundarySet q₀ b).card = (boundarySet q b).card :=
    le_antisymm hqE.2 (hmaxK q hqC)
  refine ⟨q, hqC, ?_, ?_⟩
  · intro r hr
    rw [← hqK]
    exact hmaxK r hr
  · intro r hr hrK
    apply hmaxS
    exact ⟨hr, (hqK.trans hrK.symm).le⟩

/-- Exactly the component-relative radius-sum tie-break used by the
mathematical uniqueness proof. -/
def MaxSumInComponent (p : Fin 15 → Plane) (b : ℝ) : Prop :=
  ∀ q, q ∈ connectedComponentIn (FeasibleSet15 b) p →
    boundarySet q b = boundarySet p b → radiusSum q ≤ radiusSum p

/-- The selected representative carries the exact component-relative
maximum-sum premise used by the feasible-segment lemma. -/
theorem exists_component_selected_with_maxSum
    (p : Fin 15 → Plane) (b : ℝ) (hp : p ∈ FeasibleSet15 b) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 b) p ∧
      (∀ r, r ∈ connectedComponentIn (FeasibleSet15 b) p →
        (boundarySet r b).card ≤ (boundarySet q b).card) ∧
      MaxSumInComponent q b := by
  obtain ⟨q, hq, hK, hS⟩ := exists_component_selected_packing p b hp
  refine ⟨q, hq, hK, ?_⟩
  intro r hr hboundary
  have hC : r ∈ connectedComponentIn (FeasibleSet15 b) p := by
    rw [connectedComponentIn_eq hq]
    exact hr
  exact hS r hC (congrArg Finset.card hboundary)

/-- At a terminal component, the selected representative inherits the
strict inner radial cap from the existing no-replacement theorem. The
terminal premise is stated directly, with no global maximum-count
assumption. -/
theorem exists_terminal_component_selected_with_cap
    (p : Fin 15 → Plane) (b : ℝ)
    (hp : p ∈ FeasibleSet15 b) (hb : 2 < b)
    (hterminal :
      ∀ q, q ∈ connectedComponentIn (FeasibleSet15 b) p →
        (∀ r, r ∈ connectedComponentIn (FeasibleSet15 b) p →
          (boundarySet r b).card ≤ (boundarySet q b).card) →
          NoBoundaryReplacement q b) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 b) p ∧
      MaxSumInComponent q b ∧
      (∀ i, ‖q i‖ < b → ‖q i‖ < D b) := by
  obtain ⟨q, hq, hK, hS⟩ :=
    exists_component_selected_with_maxSum p b hp
  have hqpack : InDisk b q ∧ Separated q 2 :=
    (connectedComponentIn_subset (FeasibleSet15 b) p) hq
  exact ⟨q, hq, hS,
    inner_cap_of_noBoundaryReplacement q b hb hqpack
      (hterminal q hq hK)⟩

/-- A continuous feasible segment from a configuration stays in its
component. The endpoint's sum is therefore bounded by the component
maximum whenever the boundary set is unchanged. -/
theorem radiusSum_le_of_feasible_segment_in_component
    (p : Fin 15 → Plane) (b t : ℝ) (ht : 0 ≤ t)
    (f : ℝ → Fin 15 → Plane)
    (hf : ContinuousOn f (Set.Icc 0 t))
    (hstart : f 0 = p)
    (hfeas : ∀ s ∈ Set.Icc 0 t, f s ∈ FeasibleSet15 b)
    (hmax : MaxSumInComponent p b)
    (hboundary : boundarySet (f t) b = boundarySet p b) :
    radiusSum (f t) ≤ radiusSum p := by
  have hconnected : IsConnected (f '' Set.Icc 0 t) :=
    (isConnected_Icc ht).image f hf
  have hzero : p ∈ f '' Set.Icc 0 t := by
    rw [← hstart]
    exact Set.mem_image_of_mem f ⟨le_refl _, ht⟩
  have htarget : f t ∈ f '' Set.Icc 0 t :=
    Set.mem_image_of_mem f ⟨ht, le_refl _⟩
  have hsubset : f '' Set.Icc 0 t ⊆ FeasibleSet15 b := by
    rintro q ⟨s, hs, rfl⟩
    exact hfeas s hs
  have hcomponent : f t ∈ connectedComponentIn (FeasibleSet15 b) p :=
    hconnected.2.subset_connectedComponentIn hzero hsubset htarget
  exact hmax (f t) hcomponent hboundary

/-- Exact change of the norm sum under a single-center replacement. -/
theorem radiusSum_update_center
    (p : Fin 15 → Plane) (i : Fin 15) (x : Plane) :
    radiusSum (Function.update p i x) =
      radiusSum p - ‖p i‖ + ‖x‖ := by
  classical
  unfold radiusSum
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => ‖Function.update p i x j‖) (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => ‖p j‖) (Finset.mem_univ i)]
  have herase :
      (∑ j ∈ (Finset.univ : Finset (Fin 15)).erase i,
        ‖Function.update p i x j‖) =
      (∑ j ∈ (Finset.univ : Finset (Fin 15)).erase i, ‖p j‖) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update_of_ne hji]
  rw [herase]
  simp

/-- This is the contradiction used by the radial and tangential
support arguments. It needs only a short feasible segment in the same
component, not maximality over all feasible packings. -/
theorem no_increasing_single_center_segment
    (p : Fin 15 → Plane) (b t : ℝ) (i : Fin 15)
    (x : ℝ → Plane) (ht : 0 ≤ t)
    (hf : ContinuousOn (fun s => Function.update p i (x s))
      (Set.Icc 0 t))
    (hzero : x 0 = p i)
    (hfeas : ∀ s ∈ Set.Icc 0 t,
      Function.update p i (x s) ∈ FeasibleSet15 b)
    (hmax : MaxSumInComponent p b)
    (hboundary : boundarySet (Function.update p i (x t)) b =
      boundarySet p b)
    (hgain : ‖p i‖ < ‖x t‖) : False := by
  have hstart : Function.update p i (x 0) = p := by
    rw [hzero]
    simp
  have hle := radiusSum_le_of_feasible_segment_in_component
    p b t ht (fun s => Function.update p i (x s)) hf hstart
    hfeas hmax hboundary
  rw [radiusSum_update_center] at hle
  linarith

/-- A one-center update is feasible if its new center remains in the
container and clears every unchanged center. -/
theorem feasibleSet15_update_of_pair_bounds
    (p : Fin 15 → Plane) (b : ℝ) (i : Fin 15) (z : Plane)
    (hp : p ∈ FeasibleSet15 b)
    (hz : ‖z‖ ≤ b)
    (hpairs : ∀ j, j ≠ i → 2 ≤ dist z (p j)) :
    Function.update p i z ∈ FeasibleSet15 b := by
  constructor
  · intro j
    by_cases hji : j = i
    · subst j
      simpa using hz
    · simpa [Function.update_of_ne hji] using hp.1 j
  · intro j k hjk
    by_cases hji : j = i
    · subst j
      have hki : k ≠ i := Ne.symm hjk
      simpa [Function.update_of_ne hki] using hpairs k hki
    · by_cases hki : k = i
      · subst k
        simpa [Function.update_of_ne hji, dist_comm] using hpairs j hji
      · simpa [Function.update_of_ne hji, Function.update_of_ne hki]
          using hp.2 j k hjk

/-- Linear motion of one center is continuous in the labelled
configuration space. -/
theorem continuous_single_center_linear_update
    (p : Fin 15 → Plane) (i : Fin 15) (v : Plane) :
    Continuous (fun t : ℝ => Function.update p i (p i + t • v)) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    have hcont : Continuous
        ((fun _ : ℝ => p i) + (fun t => t • v)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have heq : ((fun _ : ℝ => p i) + (fun t => t • v)) =
        (fun t => p i + t • v) := by
      funext t
      rfl
    rw [heq] at hcont
    simpa using hcont
  · simpa [Function.update_of_ne hji] using
      (continuous_const : Continuous (fun _ : ℝ => p j))

/-- The exact local support theorem needed to transfer the selected
packing exclusion chain to a component-selected representative. -/
theorem active_contact_of_component_maxSum
    (p : Fin 15 → Plane) (b : ℝ)
    (hp : p ∈ FeasibleSet15 b)
    (hmax : MaxSumInComponent p b)
    (i : Fin 15) (hi : ‖p i‖ < b)
    (v : Plane) (hv : 0 ≤ ⟪p i, v⟫_ℝ) (hvne : v ≠ 0) :
    ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      0 < ⟪p j - p i, v⟫_ℝ := by
  classical
  by_contra hnone
  let x := p i
  have hno (j : Fin 15) (hji : j ≠ i)
      (hc : dist x (p j) = 2) :
      ⟪p j - x, v⟫_ℝ ≤ 0 := by
    by_contra hbad
    exact hnone ⟨j, hji, hc, lt_of_not_ge hbad⟩
  have hpath : Continuous (fun s : ℝ => x + s • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnormevent : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖x + s • v‖ < b := by
    have htend : Filter.Tendsto (fun s : ℝ => ‖x + s • v‖)
        (𝓝 0) (𝓝 ‖x‖) := by
      simpa only [zero_smul, add_zero] using hpath.norm.tendsto 0
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (htend.eventually (eventually_lt_nhds hi))
  have hpairevent : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ j : Fin 15, j ≠ i → 2 ≤ dist (x + s • v) (p j) := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hji))
    · exact (eventually_linear_pair_separated x (p j) v
        (hp.2 i j (Ne.symm hji)) (hno j hji)).mono
          (fun _ ht _ => ht)
  let P : ℝ → Prop := fun s =>
    ‖x + s • v‖ < b ∧
      ∀ j : Fin 15, j ≠ i → 2 ≤ dist (x + s • v) (p j)
  have hPzero : P 0 := by
    constructor
    · simpa [P, x] using hi
    · intro j hji
      simpa [P, x] using hp.2 i j (Ne.symm hji)
  have hPevent : ∀ᶠ s : ℝ in 𝓝[>] 0, P s :=
    hnormevent.and hpairevent
  obtain ⟨t, ht, hsegment⟩ :=
    exists_feasible_initial_segment P hPzero hPevent
  have hfeas (s : ℝ) (hs : s ∈ Set.Icc 0 t) :
      Function.update p i (x + s • v) ∈ FeasibleSet15 b :=
    feasibleSet15_update_of_pair_bounds p b i (x + s • v) hp
      (hsegment s hs).1.le (hsegment s hs).2
  have hboundary :
      boundarySet (Function.update p i (x + t • v)) b =
        boundarySet p b := by
    have hbd := (hsegment t ⟨ht.le, le_refl t⟩).1
    ext j
    by_cases hji : j = i
    · subst j
      simp [boundarySet, ne_of_lt hi, ne_of_lt hbd]
    · simp [boundarySet, Function.update_of_ne hji]
  have hgain : ‖p i‖ < ‖x + t • v‖ := by
    have hquad : 0 < t ^ 2 * ‖v‖ ^ 2 := by
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
      positivity
    have hlin : 0 ≤ t * ⟪x, v⟫_ℝ :=
      mul_nonneg ht.le hv
    have hnormsq := norm_add_sq_real x (t • v)
    have hsq : ‖x‖ ^ 2 < ‖x + t • v‖ ^ 2 := by
      rw [hnormsq]
      simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs]
      nlinarith [sq_abs t]
    dsimp [x] at hsq
    nlinarith [norm_nonneg (p i), norm_nonneg (x + t • v)]
  exact no_increasing_single_center_segment p b t i
    (fun s => x + s • v) ht.le
    (continuous_single_center_linear_update p i v).continuousOn
    (by simp [x]) hfeas hmax hboundary hgain

/-- The strict radial blocker field of `SelectedPacking15`, derived from
component-relative maximality alone. -/
theorem strict_radial_blocker_of_component_maxSum
    (p : Fin 15 → Plane) (b : ℝ)
    (hp : p ∈ FeasibleSet15 b) (hmax : MaxSumInComponent p b)
    (i : Fin 15) (hi : ‖p i‖ < b) (hnz : p i ≠ 0) :
    ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ := by
  have hv : 0 ≤ ⟪p i, p i⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    positivity
  obtain ⟨j, hji, hc, hdot⟩ :=
    active_contact_of_component_maxSum p b hp hmax i hi (p i) hv hnz
  refine ⟨j, hji, hc, ?_⟩
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hdot
  linarith

/-- Every nonzero inner center of a component-selected representative
has active contacts on both sides of its radial ray. -/
theorem two_sided_contacts_of_component_maxSum
    (p : Fin 15 → Plane) (b : ℝ)
    (hp : p ∈ FeasibleSet15 b) (hmax : MaxSumInComponent p b)
    (i : Fin 15) (hi : ‖p i‖ < b) (hnz : p i ≠ 0) :
    (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      0 < planeCross (p i) (p j - p i)) ∧
    (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      planeCross (p i) (p j - p i) < 0) := by
  have hvne := quarterTurn_ne_zero hnz
  constructor
  · obtain ⟨j, hji, hc, hdot⟩ :=
      active_contact_of_component_maxSum p b hp hmax i hi
        (quarterTurn (p i)) (by rw [inner_quarterTurn]) hvne
    exact ⟨j, hji, hc, by simpa [inner_quarterTurn_eq_cross] using hdot⟩
  · obtain ⟨j, hji, hc, hdot⟩ :=
      active_contact_of_component_maxSum p b hp hmax i hi
        (-quarterTurn (p i))
        (by simp only [inner_neg_right, inner_quarterTurn, neg_zero]; exact le_rfl)
        (neg_ne_zero.mpr hvne)
    refine ⟨j, hji, hc, ?_⟩
    rw [inner_neg_right, inner_quarterTurn_eq_cross] at hdot
    linarith

end CP15
