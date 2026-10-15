import CP15.LocalCollisionCost
import CP15.SelectedFrontier
import CP15.ContactAngleDerivative

namespace CP15

set_option maxHeartbeats 0

/-- The outer budget for every finite family of distinct actual touching
centers. Repeated charged gaps are allowed and fully accounted for. The
baseline is a checked rational lower bound for the candidate outer angle. -/
theorem SelectedPacking15.touching_cost_budget
    {ι : Type*} [Fintype ι]
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : 7 ≤ (boundarySet p b).card)
    (inner : ι → Fin 15) (hinj : Function.Injective inner)
    (hinner : ∀ c, ‖p (inner c)‖ < b)
    (htouch : ∀ c, TouchesOuter p b (inner c)) :
    ((boundarySet p b).card : ℝ) * (57588 / 100000 : ℝ) +
      (∑ c, max 0 (2 * contactAngle b ‖p (inner c)‖ - 57588 / 100000)) ≤
        2 * Real.pi := by
  classical
  have hb : (16 / 5 : ℝ) < b := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    nlinarith [Real.sqrt_nonneg 5, h.elementaryLower]
  have hb0 : 0 < b := by linarith
  have hs : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b h.separated]
    omega
  have hDhi := D_lt_twelve_fifths_of_le_candidateB b hb0 h.belowCandidate
  choose outer houter_ne houter hcontact using htouch
  have hlo (c : ι) : (4 / 5 : ℝ) ≤ ‖p (inner c)‖ := by
    have hn := norm_sub_le (p (outer c)) (p (inner c))
    have hdist : ‖p (outer c) - p (inner c)‖ = 2 := by
      simpa [dist_eq_norm, norm_sub_rev] using hcontact c
    have hr := norm_add_le (p (outer c) - p (inner c)) (p (inner c))
    rw [sub_add_cancel, houter c, hdist] at hr
    linarith
  have hhi (c : ι) : ‖p (inner c)‖ ≤ 12 / 5 :=
    ((h.innerCap _ (hinner c)).trans hDhi).le
  have hlocal (c : ι) := SevenBoundary.actual_contact_local_gap_position
    p b (by linarith) h.belowCandidate h.separated h.innerCap hK
    (inner c) (outer c) (hinner c) (houter c) (hcontact c)
  choose charge θ δ hlift hδ0 hsupport hposition hcos using hlocal
  have hδπ (c : ι) : δ c ≤ Real.pi := by
    have hg := SevenBoundary.every_next_gap_lt_pi p b hb0
      h.belowCandidate h.separated hK (charge c)
    linarith [hsupport c, Real.pi_pos]
  have hlaw (c : ι) : 2 * ‖p (inner c)‖ * b * Real.cos (δ c) =
      b ^ 2 + ‖p (inner c)‖ ^ 2 - 4 := by
    have hc := contact_inner_formula (p (inner c)) (p (outer c)) b
      ‖p (inner c)‖ rfl (houter c) (hcontact c)
    rw [polar_inner, houter c, ← hcos c] at hc
    nlinarith
  have hδsmall (c : ι) : δ c ≤ 13 / 20 :=
    (capped_contact_offset_lt_13_div_20 b ‖p (inner c)‖ (δ c) hb
      (by linarith [hlo c]) (h.innerCap _ (hinner c)) (hδ0 c) (hδπ c) (hlaw c)).le
  have hδexact (c : ι) : δ c = contactAngle b ‖p (inner c)‖ := by
    have hfactor : 0 < 2 * b * ‖p (inner c)‖ := by
      have := hlo c
      positivity
    have hc : Real.cos (δ c) = contactCos b ‖p (inner c)‖ := by
      unfold contactCos
      apply (eq_div_iff hfactor.ne').2
      nlinarith [hlaw c]
    unfold contactAngle
    rw [← hc, Real.arccos_cos (hδ0 c) (hδπ c)]
  have hangle (c d : ι) (hcd : c ≠ d) :
      (4 / 5 : ℝ) < |θ c - θ d| := by
    have hc := cos_diff_of_two_pi_lifts (p (inner c)) (p (inner d))
      (θ c) (θ d) (hlift c) (hlift d)
    have hcabs : Real.cos (polarArg (p (inner c)) - polarArg (p (inner d))) =
        Real.cos |θ c - θ d| := by rw [Real.cos_abs]; exact hc
    exact touching_annulus_pair_angle_gt_four_fifths _ _ |θ c - θ d|
      (hlo c) (hhi c) (hlo d) (hhi d)
      (h.separated _ _ (hinj.ne hcd)) hcabs (abs_nonneg _)
  let extra : ι → ℝ := fun c => max 0 (2 * δ c - 57588 / 100000)
  have hgap (u : Fin (boundaryAngles p b).card) :
      (∑ c ∈ Finset.univ.filter (fun c => charge c = u), extra c) ≤
        nextBoundaryGap p b hs u - 57588 / 100000 := by
    let left := (boundaryAngles p b).orderEmbOfFin rfl u
    let right := left + nextBoundaryGap p b hs u
    have hdiff : nextBoundaryGap p b hs u = right - left := by
      dsimp [right]
      ring
    rw [hdiff]
    apply local_collision_extra_cost_le (Finset.univ.filter (fun c => charge c = u))
      left right (57588 / 100000) θ δ (by norm_num) (by norm_num) (by norm_num)
    · dsimp [right]
      linarith [every_next_gap_ge_57588_div_100000 p b hb0
        h.belowCandidate h.separated hs u]
    · intro c _
      exact ⟨hδ0 c, hδsmall c⟩
    · intro c hc
      have heq := (Finset.mem_filter.mp hc).2
      dsimp [right]
      simpa [heq] using hsupport c
    · intro c hc
      have heq := (Finset.mem_filter.mp hc).2
      simpa [left, right, heq] using hposition c
    · intro c _ d _ hcd
      exact hangle c d hcd
  have hpartition :
      (∑ u : Fin (boundaryAngles p b).card,
        ∑ c ∈ Finset.univ.filter (fun c => charge c = u), extra c) = ∑ c, extra c := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hgap u)
  rw [hpartition, Finset.sum_sub_distrib, sum_next_boundary_gaps p b hs] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [boundaryAngles_card p b h.separated] at hsum
  have hext : (∑ c, extra c) =
      ∑ c, max 0 (2 * contactAngle b ‖p (inner c)‖ - 57588 / 100000) := by
    apply Finset.sum_congr rfl
    intro c _
    simp [extra, hδexact c]
  rw [hext] at hsum
  linarith

end CP15
