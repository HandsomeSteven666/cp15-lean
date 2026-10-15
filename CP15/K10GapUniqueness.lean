import CP15.K10BasicGeometry

namespace CP15

set_option maxHeartbeats 0

/-- The two actual contact positions cannot share an outer gap shorter
than 1.11 radians. Low/low radii require more than 1.15 radians; every
other collision has an offset sum above .4 and clearance above .8. -/
theorem SelectedPacking15.two_touching_in_short_gap_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (i j : Fin 15) (hij : i ≠ j)
    (hi : ‖p i‖ < b) (hj : ‖p j‖ < b)
    (hti : TouchesOuter p b i) (htj : TouchesOuter p b j)
    (left right θi θj δi δj : ℝ) (hgap : right - left < 111 / 100)
    (hlifti : θi = polarArg (p i) ∨ θi = polarArg (p i) + 2 * Real.pi)
    (hliftj : θj = polarArg (p j) ∨ θj = polarArg (p j) + 2 * Real.pi)
    (hδi : 0 ≤ δi ∧ δi ≤ 13 / 20) (hδj : 0 ≤ δj ∧ δj ≤ 13 / 20)
    (hδiex : δi = contactAngle b ‖p i‖) (hδjex : δj = contactAngle b ‖p j‖)
    (hsupi : 2 * δi ≤ right - left) (hsupj : 2 * δj ≤ right - left)
    (hposi : θi = left + δi ∨ θi = right - δi)
    (hposj : θj = left + δj ∨ θj = right - δj) : False := by
  have hb : 0 < b := by have hc := centerFeasible_radius_gt_two h.optimal.1; linarith
  have hri := (h.touching_radius_gt_123_div_100 i hi hti).le
  have hrj := (h.touching_radius_gt_123_div_100 j hj htj).le
  have hriHi := ((h.innerCap i hi).trans
    (D_lt_twelve_fifths_of_le_candidateB b hb h.belowCandidate)).le
  have hrjHi := ((h.innerCap j hj).trans
    (D_lt_twelve_fifths_of_le_candidateB b hb h.belowCandidate)).le
  have hcos : Real.cos (polarArg (p i) - polarArg (p j)) = Real.cos |θi - θj| := by
    rw [Real.cos_abs]
    exact cos_diff_of_two_pi_lifts _ _ _ _ hlifti hliftj
  have hsep := touching_annulus_pair_angle_gt_four_fifths (p i) (p j) |θi - θj|
    (by linarith) hriHi (by linarith) hrjHi (h.separated i j hij) hcos (abs_nonneg _)
  have hθi : left ≤ θi ∧ θi ≤ right := by
    rcases hposi with hx | hx <;> constructor <;> rw [hx] <;> linarith [hδi.1]
  have hθj : left ≤ θj ∧ θj ≤ right := by
    rcases hposj with hx | hx <;> constructor <;> rw [hx] <;> linarith [hδj.1]
  have habs : |θi - θj| ≤ right - left := by
    apply abs_le.mpr
    constructor <;> linarith [hθi.1, hθi.2, hθj.1, hθj.2]
  have hnotBoth : ¬(‖p i‖ ≤ (9 / 5 : ℝ) ∧ ‖p j‖ ≤ (9 / 5 : ℝ)) := by
    rintro ⟨hloi, hloj⟩
    have ha := low_touching_pair_angle_gt_23_div_20 (p i) (p j) |θi - θj|
      hri hloi hrj hloj (h.separated i j hij) hcos (abs_nonneg _)
    linarith
  have hδsum : (2 / 5 : ℝ) < δi + δj := by
    by_cases hlow : ‖p i‖ ≤ (9 / 5 : ℝ)
    · have hhigh : (9 / 5 : ℝ) < ‖p j‖ := lt_of_not_ge (fun hjl => hnotBoth ⟨hlow, hjl⟩)
      have hγ := h.touching_angle_gt_of_rational_corner j hj htj (9 / 5) (2 / 5)
        (by norm_num) hhigh.le (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])
      rw [← hδjex] at hγ
      linarith [hδi.1]
    · have hhigh := (lt_of_not_ge hlow).le
      have hγ := h.touching_angle_gt_of_rational_corner i hi hti (9 / 5) (2 / 5)
        (by norm_num) hhigh (by norm_num) (by norm_num) (by norm_num [contactCos, sinCubicUpper])
      rw [← hδiex] at hγ
      linarith [hδj.1]
  rcases hposi with hil | hir <;> rcases hposj with hjl | hjr
  · have hc : |θi - θj| ≤ 13 / 20 := by
      apply abs_le.mpr
      constructor <;> rw [hil, hjl] <;> linarith [hδi.1, hδi.2, hδj.1, hδj.2]
    linarith
  · have hord : θi ≤ θj := by rw [hil, hjr]; linarith
    have heq : |θi - θj| = θj - θi := by rw [abs_of_nonpos (by linarith)]; ring
    rw [heq, hil, hjr] at hsep
    linarith
  · have hord : θj ≤ θi := by rw [hir, hjl]; linarith
    have heq : |θi - θj| = θi - θj := abs_of_nonneg (by linarith)
    rw [heq, hir, hjl] at hsep
    linarith
  · have hc : |θi - θj| ≤ 13 / 20 := by
      apply abs_le.mpr
      constructor <;> rw [hir, hjr] <;> linarith [hδi.1, hδi.2, hδj.1, hδj.2]
    linarith

/-- Every actual touching center has an occupied outer gap, with exact
contact offset and both endpoint margins. In K=10 the occupied gaps are
distinct for every family of distinct touching centers. -/
theorem SelectedPacking15.K10_injective_touching_gap_assignment
    {ι : Type*} {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10)
    (inner : ι → Fin 15) (hinj : Function.Injective inner)
    (hinner : ∀ c, ‖p (inner c)‖ < b) (htouch : ∀ c, TouchesOuter p b (inner c))
    (hs : 2 ≤ (boundaryAngles p b).card) :
    ∃ charge : ι → Fin (boundaryAngles p b).card, ∃ θ δ : ι → ℝ,
      Function.Injective charge ∧ ∀ c,
        (θ c = polarArg (p (inner c)) ∨ θ c = polarArg (p (inner c)) + 2 * Real.pi) ∧
        δ c = contactAngle b ‖p (inner c)‖ ∧ (0 ≤ δ c ∧ δ c ≤ 13 / 20) ∧
        2 * δ c ≤ nextBoundaryGap p b hs (charge c) ∧
        (θ c = (boundaryAngles p b).orderEmbOfFin rfl (charge c) + δ c ∨
          θ c = (boundaryAngles p b).orderEmbOfFin rfl (charge c) +
            nextBoundaryGap p b hs (charge c) - δ c) := by
  classical
  have hb : (16 / 5 : ℝ) < b := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sqrt_nonneg 5, h.elementaryLower]
  choose outer houter_ne houter hcontact using htouch
  have hTouch (c : ι) : TouchesOuter p b (inner c) :=
    ⟨outer c, houter_ne c, houter c, hcontact c⟩
  have hlocal (c : ι) := SevenBoundary.actual_contact_local_gap_position
    p b (by linarith) h.belowCandidate h.separated h.innerCap (by omega)
    (inner c) (outer c) (hinner c) (houter c) (hcontact c)
  choose charge θ δ hlift hδ0 hsupport hposition hcos using hlocal
  have hδπ (c : ι) : δ c ≤ Real.pi := by
    have hg := h.K10_next_gap_lt_111_div_100 hK hs (charge c)
    linarith [hsupport c, Real.pi_gt_three]
  have hlaw (c : ι) : 2 * ‖p (inner c)‖ * b * Real.cos (δ c) =
      b ^ 2 + ‖p (inner c)‖ ^ 2 - 4 := by
    have hc := contact_inner_formula (p (inner c)) (p (outer c)) b
      ‖p (inner c)‖ rfl (houter c) (hcontact c)
    rw [polar_inner, houter c, ← hcos c] at hc
    nlinarith
  have hrad (c : ι) := h.touching_radius_gt_123_div_100 (inner c) (hinner c) (hTouch c)
  have hδsmall (c : ι) : δ c ≤ 13 / 20 :=
    (capped_contact_offset_lt_13_div_20 b ‖p (inner c)‖ (δ c) hb
      (by linarith [hrad c]) (h.innerCap _ (hinner c)) (hδ0 c) (hδπ c) (hlaw c)).le
  have hδexact (c : ι) : δ c = contactAngle b ‖p (inner c)‖ := by
    have hfactor : 0 < 2 * b * ‖p (inner c)‖ := by
      have hr := hrad c
      positivity
    have hc : Real.cos (δ c) = contactCos b ‖p (inner c)‖ := by
      unfold contactCos
      apply (eq_div_iff hfactor.ne').2
      nlinarith [hlaw c]
    unfold contactAngle
    rw [← hc, Real.arccos_cos (hδ0 c) (hδπ c)]
  have hcharge : Function.Injective charge := by
    intro c d heq
    by_contra hne
    let left := (boundaryAngles p b).orderEmbOfFin rfl (charge c)
    let right := left + nextBoundaryGap p b hs (charge c)
    have hsupd := hsupport d
    have hposd := hposition d
    rw [← heq] at hsupd hposd
    apply h.two_touching_in_short_gap_impossible (inner c) (inner d) (hinj.ne hne)
      (hinner c) (hinner d) (hTouch c) (hTouch d) left right (θ c) (θ d) (δ c) (δ d)
    · dsimp [right]
      linarith [h.K10_next_gap_lt_111_div_100 hK hs (charge c)]
    · exact hlift c
    · exact hlift d
    · exact ⟨hδ0 c, hδsmall c⟩
    · exact ⟨hδ0 d, hδsmall d⟩
    · exact hδexact c
    · exact hδexact d
    · dsimp [right]
      linarith [hsupport c]
    · dsimp [right]
      linarith [hsupd]
    · simpa [left, right] using hposition c
    · simpa [left, right] using hposd
  exact ⟨charge, θ, δ, hcharge,
    fun c => ⟨hlift c, hδexact c, ⟨hδ0 c, hδsmall c⟩, hsupport c, hposition c⟩⟩

end CP15
