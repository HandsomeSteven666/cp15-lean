import CP15.ContactAssignment

namespace CP15

/-- The gap after one boundary point is the gap before the next point. -/
theorem next_gap_eq_previous_succ (p : Fin 15 → Plane) (b : ℝ)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (u : Fin (boundaryAngles p b).card)
    (hu : u.val + 1 < (boundaryAngles p b).card) :
    nextBoundaryGap p b hK u =
      previousBoundaryGap p b hK ⟨u.val + 1, hu⟩ := by
  simp [nextBoundaryGap, previousBoundaryGap, hu]

/-- The forward gap at the last point is the backward gap at the first. -/
theorem next_last_eq_previous_first (p : Fin 15 → Plane) (b : ℝ)
    (hK : 2 ≤ (boundaryAngles p b).card) :
    nextBoundaryGap p b hK
        ⟨(boundaryAngles p b).card - 1, by omega⟩ =
      previousBoundaryGap p b hK ⟨0, by omega⟩ := by
  have hnot : ¬ (boundaryAngles p b).card - 1 + 1 <
      (boundaryAngles p b).card := by omega
  simp [nextBoundaryGap, previousBoundaryGap, hnot]

/-- Canonicalize a backward charge as a forward charge to the same cyclic
gap. This covers the first/last wrap without a special downstream case. -/
theorem previous_gap_has_next_index (p : Fin 15 → Plane) (b : ℝ)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (u : Fin (boundaryAngles p b).card) :
    ∃ v : Fin (boundaryAngles p b).card,
      previousBoundaryGap p b hK u = nextBoundaryGap p b hK v := by
  by_cases hu : 0 < u.val
  · have hv : u.val - 1 < (boundaryAngles p b).card := by
      have := u.isLt
      omega
    let v : Fin (boundaryAngles p b).card := ⟨u.val - 1, hv⟩
    have hsucc : v.val + 1 < (boundaryAngles p b).card := by
      dsimp [v]
      omega
    refine ⟨v, ?_⟩
    have hindex : (⟨v.val + 1, hsucc⟩ :
        Fin (boundaryAngles p b).card) = u := by
      apply Fin.ext
      dsimp [v]
      omega
    rw [← hindex]
    exact (next_gap_eq_previous_succ p b hK v hsucc).symm
  · have hzero : u.val = 0 := by omega
    have hfirst : u = (⟨0, by omega⟩ : Fin (boundaryAngles p b).card) :=
      Fin.ext hzero
    refine ⟨⟨(boundaryAngles p b).card - 1, by omega⟩, ?_⟩
    rw [hfirst]
    exact (next_last_eq_previous_first p b hK).symm

/-- Every inner–outer contact charges one canonical forward gap. The
nonnegative offset is one of the four explicit real lifts of its polar
difference. No uniqueness of the charged index is asserted. -/
theorem every_outer_contact_charges_canonical_gap (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hcontact : dist (p i) (p j) = 2) :
    ∃ (v : Fin (boundaryAngles p b).card) (δ : ℝ),
      0 ≤ δ ∧
      2 * δ ≤ nextBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) v ∧
      (δ = polarArg (p i) - polarArg (p j) ∨
       δ = polarArg (p j) - polarArg (p i) ∨
       δ = polarArg (p i) + 2 * Real.pi - polarArg (p j) ∨
       δ = polarArg (p j) + 2 * Real.pi - polarArg (p i)) := by
  let hsize : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  obtain ⟨u, _, hforward | hbackward | hplus | hminus⟩ :=
    every_outer_contact_charges_adjacent_gap p b hb hbB hsep hD hK
      i j hi hj hcontact
  · refine ⟨u, polarArg (p i) - polarArg (p j), by linarith [hforward.1], ?_,
      Or.inl rfl⟩
    exact hforward.2
  · obtain ⟨v, hv⟩ := previous_gap_has_next_index p b hsize u
    refine ⟨v, polarArg (p j) - polarArg (p i), by linarith [hbackward.1], ?_,
      Or.inr (Or.inl rfl)⟩
    rw [← hv]
    exact hbackward.2
  · refine ⟨u, polarArg (p i) + 2 * Real.pi - polarArg (p j),
      by linarith [hplus.1], ?_, Or.inr (Or.inr (Or.inl rfl))⟩
    exact hplus.2
  · obtain ⟨v, hv⟩ := previous_gap_has_next_index p b hsize u
    refine ⟨v, polarArg (p j) + 2 * Real.pi - polarArg (p i),
      by linarith [hminus.1], ?_, Or.inr (Or.inr (Or.inr rfl))⟩
    rw [← hv]
    exact hminus.2

/-- Every canonical gap has the lower bound already established for the
actual sorted boundary points. -/
theorem every_next_gap_ge_four_sevenths (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (u : Fin (boundaryAngles p b).card) :
    (4 / 7 : ℝ) ≤ nextBoundaryGap p b hK u := by
  by_cases hu : u.val + 1 < (boundaryAngles p b).card
  · have hlt : u < (⟨u.val + 1, hu⟩ : Fin (boundaryAngles p b).card) := by
      change u.val < u.val + 1
      omega
    simpa [nextBoundaryGap, hu] using
      ordered_boundary_angle_gap_ge_four_sevenths p b hb hbB hsep
        u ⟨u.val + 1, hu⟩ hlt
  · have huval : u.val = (boundaryAngles p b).card - 1 := by
      have := u.isLt
      omega
    have hlast : u = (⟨(boundaryAngles p b).card - 1, by omega⟩ :
        Fin (boundaryAngles p b).card) := Fin.ext huval
    have hnot : ¬ (boundaryAngles p b).card - 1 + 1 <
        (boundaryAngles p b).card := by omega
    simpa [nextBoundaryGap, hlast, hnot] using
      ordered_boundary_wrap_gap_ge_four_sevenths p b hb hbB hsep hK

/-- Every canonical gap is short when there are at least nine boundary
centers. -/
theorem every_next_gap_lt_pi (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 9 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card) :
    nextBoundaryGap p b
      (by rw [boundaryAngles_card p b hsep]; omega) u < Real.pi := by
  by_cases hu : u.val + 1 < (boundaryAngles p b).card
  · simpa [nextBoundaryGap, hu] using
      ordered_boundary_adjacent_gap_lt_pi p b hb hbB hsep hK u hu
  · have huval : u.val = (boundaryAngles p b).card - 1 := by
      have := u.isLt
      omega
    have hlast : u = (⟨(boundaryAngles p b).card - 1, by
        rw [boundaryAngles_card p b hsep]; omega⟩ :
        Fin (boundaryAngles p b).card) := Fin.ext huval
    have hnot : ¬ (boundaryAngles p b).card - 1 + 1 <
        (boundaryAngles p b).card := by omega
    simpa [nextBoundaryGap, hlast, hnot] using
      ordered_boundary_wrap_gap_lt_pi p b hb hbB hsep hK

/-- The charged offset is the genuine short circular angle: its cosine is
the cosine of the polar argument difference, and it lies in `[0,π/2)`. -/
theorem outer_contact_short_offset_exists (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hcontact : dist (p i) (p j) = 2) :
    ∃ (v : Fin (boundaryAngles p b).card) (δ : ℝ),
      0 ≤ δ ∧ δ < Real.pi / 2 ∧
      Real.cos δ = Real.cos (polarArg (p i) - polarArg (p j)) ∧
      2 * δ ≤ nextBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) v := by
  obtain ⟨v, δ, hδ0, hsupport, hform⟩ :=
    every_outer_contact_charges_canonical_gap p b hb hbB hsep hD hK
      i j hi hj hcontact
  have hshort := every_next_gap_lt_pi p b (by linarith) hbB hsep hK v
  have hδshort : δ < Real.pi / 2 := by linarith
  refine ⟨v, δ, hδ0, hδshort, ?_, hsupport⟩
  rcases hform with hform | hform | hform | hform
  · rw [hform]
  · rw [hform]
    have hneg : polarArg (p j) - polarArg (p i) =
        -(polarArg (p i) - polarArg (p j)) := by ring
    rw [hneg, Real.cos_neg]
  · rw [hform, cos_add_two_pi_sub_left]
  · rw [hform, cos_add_two_pi_sub_left]
    have hneg : polarArg (p j) - polarArg (p i) =
        -(polarArg (p i) - polarArg (p j)) := by ring
    rw [hneg, Real.cos_neg]

/-- Exact contact cosine law for the offset that charges an actual cyclic
gap. This is the algebraic interface for later quantitative support bounds. -/
theorem outer_contact_charged_cosine_law (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hcontact : dist (p i) (p j) = 2) :
    ∃ (v : Fin (boundaryAngles p b).card) (δ : ℝ),
      0 ≤ δ ∧ δ < Real.pi / 2 ∧
      2 * δ ≤ nextBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) v ∧
      2 * ‖p i‖ * b * Real.cos δ =
        b ^ 2 + ‖p i‖ ^ 2 - 4 := by
  obtain ⟨v, δ, hδ0, hδshort, hcos, hgap⟩ :=
    outer_contact_short_offset_exists p b hb hbB hsep hD hK
      i j hi hj hcontact
  refine ⟨v, δ, hδ0, hδshort, hgap, ?_⟩
  have hcontact' := contact_inner_formula (p i) (p j) b ‖p i‖
    rfl hj hcontact
  rw [polar_inner, hj, ← hcos] at hcontact'
  nlinarith

/-- A ring-touching inner center of radius at least two charges a gap at
twice an offset whose cosine is bounded by `b/4`. This is the exact support
bound before converting it to an arccosine lower bound. -/
theorem outer_contact_radius_two_cos_support (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hs : 2 ≤ ‖p i‖)
    (hj : ‖p j‖ = b) (hcontact : dist (p i) (p j) = 2) :
    ∃ (v : Fin (boundaryAngles p b).card) (δ : ℝ),
      0 ≤ δ ∧ δ < Real.pi / 2 ∧
      2 * δ ≤ nextBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) v ∧
      Real.cos δ ≤ b / 4 := by
  obtain ⟨v, δ, hδ0, hδshort, hgap, hlaw⟩ :=
    outer_contact_charged_cosine_law p b hb hbB hsep hD hK
      i j hi hj hcontact
  refine ⟨v, δ, hδ0, hδshort, hgap, ?_⟩
  exact contact_offset_cos_le_b_div_four b ‖p i‖ δ hb hs (hD i hi) hlaw

/-- A radius-at-least-two inner contact forces an actual cyclic gap to
contain twice the explicit arccosine angle. No numerical approximation is
used, and the statement does not assign distinct gaps to different centers. -/
theorem outer_contact_radius_two_gap_support (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hs : 2 ≤ ‖p i‖)
    (hj : ‖p j‖ = b) (hcontact : dist (p i) (p j) = 2) :
    ∃ v : Fin (boundaryAngles p b).card,
      2 * Real.arccos (b / 4) ≤ nextBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) v := by
  obtain ⟨v, δ, hδ0, hδshort, hgap, hcos⟩ :=
    outer_contact_radius_two_cos_support p b hb hbB hsep hD hK
      i j hi hs hj hcontact
  have hangle : Real.arccos (b / 4) ≤ δ := by
    calc
      Real.arccos (b / 4) ≤ Real.arccos (Real.cos δ) :=
        Real.arccos_le_arccos hcos
      _ = δ := Real.arccos_cos hδ0 (by linarith)
  exact ⟨v, by linarith⟩

/-- The exact sum of the cyclic gaps of actual boundary centers is `2π`.
This statement is independent of separation and of any contact selection. -/
theorem sum_next_boundary_gaps (p : Fin 15 → Plane) (b : ℝ)
    (hK : 2 ≤ (boundaryAngles p b).card) :
    ∑ u : Fin (boundaryAngles p b).card,
      nextBoundaryGap p b hK u = 2 * Real.pi := by
  let s := boundaryAngles p b
  have hsK : 2 ≤ s.card := hK
  let e := s.orderEmbOfFin rfl
  let first : Fin s.card := ⟨0, by omega⟩
  let last : Fin s.card := ⟨s.card - 1, by omega⟩
  let f : ℕ → ℝ := fun n => if hn : n < s.card then e ⟨n, hn⟩ else e last
  let g : ℕ → ℝ := fun n => if hn : n < s.card then
      nextBoundaryGap p b hK ⟨n, by simpa [s] using hn⟩ else 0
  have hstep (n : ℕ) (hn : n < s.card - 1) :
      g n = f (n + 1) - f n := by
    have hn0 : n < s.card := by omega
    have hn1 : n + 1 < s.card := by omega
    simp [g, nextBoundaryGap, f, hn0, hn1, s, e]
  have hlast : g (s.card - 1) =
      f 0 + 2 * Real.pi - f (s.card - 1) := by
    have hnot : ¬ s.card - 1 + 1 < s.card := by omega
    have hzero : 0 < s.card := by omega
    have hlast' : s.card - 1 < s.card := by omega
    simp [g, nextBoundaryGap, f, hnot, hzero, hlast', last, s, e]
  have hfin : (∑ u : Fin s.card, nextBoundaryGap p b hK u) =
      ∑ u : Fin s.card, g u.val := by
    apply Finset.sum_congr rfl
    intro u _
    simp [g, u.isLt]
  rw [hfin, Fin.sum_univ_eq_sum_range g]
  have hscard : s.card = (s.card - 1) + 1 := by omega
  rw [hscard, Finset.sum_range_succ]
  have hsum : (∑ n ∈ Finset.range (s.card - 1), g n) =
        f (s.card - 1) - f 0 := by
    calc
      (∑ n ∈ Finset.range (s.card - 1), g n) =
          ∑ n ∈ Finset.range (s.card - 1), (f (n + 1) - f n) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hstep n (Finset.mem_range.mp hn)
      _ = f (s.card - 1) - f 0 := Finset.sum_range_sub f (s.card - 1)
  rw [hsum]
  rw [hlast]
  ring

/-- Exact cyclic budget for a set of *distinct* charged gaps. The geometry
must separately prove that its chosen charges really have distinct indices;
this lemma makes that prerequisite explicit. -/
theorem charged_gap_budget (p : Fin 15 → Plane) (b α : ℝ)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (charged : Finset (Fin (boundaryAngles p b).card))
    (support : Fin (boundaryAngles p b).card → ℝ)
    (hcharged : ∀ u ∈ charged,
      2 * support u ≤ nextBoundaryGap p b hK u)
    (hother : ∀ u ∈ Finset.univ \ charged,
      α ≤ nextBoundaryGap p b hK u) :
    (∑ u ∈ charged, 2 * support u) +
      (∑ u ∈ Finset.univ \ charged, α) ≤ 2 * Real.pi := by
  have hfirst : (∑ u ∈ charged, 2 * support u) ≤
      ∑ u ∈ charged, nextBoundaryGap p b hK u :=
    Finset.sum_le_sum hcharged
  have hsecond : (∑ u ∈ Finset.univ \ charged, α) ≤
      ∑ u ∈ Finset.univ \ charged, nextBoundaryGap p b hK u :=
    Finset.sum_le_sum hother
  have hdisj : Disjoint charged (Finset.univ \ charged) :=
    Finset.disjoint_sdiff
  have hcover : charged ∪ (Finset.univ \ charged) = Finset.univ := by
    simp
  have hsum : (∑ u ∈ charged, nextBoundaryGap p b hK u) +
      (∑ u ∈ Finset.univ \ charged, nextBoundaryGap p b hK u) =
        ∑ u : Fin (boundaryAngles p b).card, nextBoundaryGap p b hK u := by
    rw [← Finset.sum_union hdisj, hcover]
  linarith [sum_next_boundary_gaps p b hK]

/-- Apply the canonical budget to actual boundary gaps at the candidate
scale. The caller must establish the selected support and distinctness. -/
theorem charged_gap_budget_four_sevenths (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (charged : Finset (Fin (boundaryAngles p b).card))
    (support : Fin (boundaryAngles p b).card → ℝ)
    (hcharged : ∀ u ∈ charged,
      2 * support u ≤ nextBoundaryGap p b hK u) :
    (∑ u ∈ charged, 2 * support u) +
      (∑ _u ∈ Finset.univ \ charged, (4 / 7 : ℝ)) ≤
        2 * Real.pi := by
  exact charged_gap_budget p b (4 / 7) hK charged support hcharged
    (fun u _ => every_next_gap_ge_four_sevenths p b hb hbB hsep hK u)

end CP15

