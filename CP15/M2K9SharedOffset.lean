import CP15.M2K9SharedGap
import CP15.M2K9AngleBounds

namespace CP15

noncomputable def sharedOffset (s δ : ℝ) : ℝ :=
  Real.arctan (2 * Real.sin δ / (s - 2 * Real.cos δ))

noncomputable def sharedOffsetDerivative (s δ : ℝ) : ℝ :=
  2 * (s * Real.cos δ - 2) / (s ^ 2 + 4 - 4 * s * Real.cos δ)

noncomputable def sharedOffsetSecondDerivative (s δ : ℝ) : ℝ :=
  -2 * s * (s ^ 2 - 4) * Real.sin δ /
    (s ^ 2 + 4 - 4 * s * Real.cos δ) ^ 2

noncomputable def sharedEndpointX : ℝ :=
  D candidateB - (2 + Real.sqrt 3 * F candidateB) / D candidateB

noncomputable def sharedEndpointY : ℝ :=
  (2 * Real.sqrt 3 - F candidateB) / D candidateB

noncomputable def sharedEndpointR : ℝ :=
  Real.sqrt (sharedEndpointX ^ 2 + sharedEndpointY ^ 2)

noncomputable def sharedEndpointKappa : ℝ :=
  Real.arccos (2 / D candidateB)

noncomputable def sharedEndpointLowDelta : ℝ :=
  Real.pi / 3 - sharedEndpointKappa

noncomputable def sharedEndpointAngle : ℝ :=
  sharedOffset (D candidateB) sharedEndpointLowDelta +
    sharedOffset (D candidateB) sharedEndpointKappa

private theorem shared_candidateB_tight_bounds :
    (3521356 / 1000000 : ℝ) < candidateB ∧
      candidateB < 352136 / 100000 := by
  have hr5sq : Candidate.root5 ^ 2 = 5 := Candidate.root5_sq
  have hr5pos : 0 < Candidate.root5 := Candidate.root5_pos
  have hr5lo : (2236067 / 1000000 : ℝ) < Candidate.root5 := by
    have hn := Real.sqrt_nonneg 5
    nlinarith
  have hr5hi : Candidate.root5 < (2236068 / 1000000 : ℝ) := by
    have hn := Real.sqrt_nonneg 5
    nlinarith
  have hqlo : (894427 / 1000000 : ℝ) < 2 / Candidate.root5 := by
    apply (lt_div_iff₀ hr5pos).2
    nlinarith
  have hradlo : 0 ≤ 1 + 2 / Candidate.root5 := by positivity
  have hrootlo : (1376381 / 1000000 : ℝ) <
      Real.sqrt (1 + 2 / Candidate.root5) := by
    have hsq := Real.sq_sqrt hradlo
    have hn := Real.sqrt_nonneg (1 + 2 / Candidate.root5)
    nlinarith
  have hBsq : candidateB ^ 2 = 6 + 2 / Candidate.root5 +
      4 * Real.sqrt (1 + 2 / Candidate.root5) := by
    unfold candidateB Candidate.root5
    rw [Real.sq_sqrt]
    positivity
  have hBnonneg : 0 ≤ candidateB := candidateB_pos.le
  constructor
  · nlinarith
  · exact Candidate.candidateB_lt_352136_div_100000

private theorem shared_endpoint_scalar_boxes :
    (2385429 / 1000000 : ℝ) < D candidateB ∧
      D candidateB < 2385436 / 1000000 ∧
      (130008 / 100000 : ℝ) < F candidateB ∧
      F candidateB < 130013 / 100000 := by
  obtain ⟨hBlo, hBhi⟩ := shared_candidateB_tight_bounds
  have hBpos := candidateB_pos
  have hDlo : (2385429 / 1000000 : ℝ) < D candidateB := by
    unfold D
    have hmul : 4 / candidateB < candidateB - 2385429 / 1000000 := by
      apply (div_lt_iff₀ hBpos).2
      nlinarith [sq_nonneg (candidateB - 3521356 / 1000000)]
    linarith
  have hDhi : D candidateB < 2385436 / 1000000 := by
    unfold D
    have hmul : candidateB - 2385436 / 1000000 <
        4 / candidateB := by
      apply (lt_div_iff₀ hBpos).2
      nlinarith [sq_nonneg (candidateB - 352136 / 100000)]
    linarith
  have hDpos : 0 < D candidateB := by linarith
  have hrad : 0 ≤ D candidateB ^ 2 - 4 := by
    nlinarith [sq_nonneg (D candidateB - 2)]
  have hFsq : F candidateB ^ 2 = D candidateB ^ 2 - 4 := by
    unfold F
    exact Real.sq_sqrt hrad
  have hFlo : (130008 / 100000 : ℝ) < F candidateB := by
    have hFnon : 0 ≤ F candidateB := by unfold F; exact Real.sqrt_nonneg _
    have hdSq : (2385429 / 1000000 : ℝ) ^ 2 < D candidateB ^ 2 := by
      exact (sq_lt_sq₀ (by norm_num) (by linarith) |>.2 hDlo)
    nlinarith [hdSq, hFnon]
  have hFhi : F candidateB < (130013 / 100000 : ℝ) := by
    have hFnon : 0 ≤ F candidateB := by unfold F; exact Real.sqrt_nonneg _
    have hdSq : D candidateB ^ 2 < (2385436 / 1000000 : ℝ) ^ 2 := by
      exact (sq_lt_sq₀ (by linarith) (by norm_num) |>.2 hDhi)
    nlinarith [hdSq, hFnon]
  exact ⟨hDlo, hDhi, hFlo, hFhi⟩

private theorem shared_endpoint_coordinate_boxes :
    (3 / 5 : ℝ) < sharedEndpointX ∧
      sharedEndpointX < 6031 / 10000 ∧
      (9071 / 10000 : ℝ) < sharedEndpointY ∧
      sharedEndpointY < 9072 / 10000 ∧
      sharedEndpointR < 109 / 100 := by
  obtain ⟨hDlo, hDhi, hFlo, hFhi⟩ := shared_endpoint_scalar_boxes
  have hglo : (173205 / 100000 : ℝ) < Real.sqrt 3 := by
    have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg 3
    nlinarith
  have hghi : Real.sqrt 3 < (173206 / 100000 : ℝ) := by
    have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg 3
    nlinarith
  have hDpos : 0 < D candidateB := by linarith
  have hFpos : 0 < F candidateB := by linarith
  have hgpos : 0 < Real.sqrt 3 := by positivity
  have hGFlo : (173205 / 100000 : ℝ) *
      (130008 / 100000 : ℝ) < Real.sqrt 3 * F candidateB := by
    have h₁ := mul_lt_mul_of_pos_right hglo (by norm_num : (0 : ℝ) < 130008 / 100000)
    have h₂ := mul_lt_mul_of_pos_left hFlo hgpos
    linarith
  have hGFhi : Real.sqrt 3 * F candidateB <
      (173206 / 100000 : ℝ) * (130013 / 100000 : ℝ) := by
    have h₁ := mul_lt_mul_of_pos_right hghi hFpos
    have h₂ := mul_lt_mul_of_pos_left hFhi
      (by norm_num : (0 : ℝ) < 173206 / 100000)
    linarith
  have hDsqlo : (2385429 / 1000000 : ℝ) ^ 2 <
      D candidateB ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by linarith)).2 hDlo
  have hDsquarehi : D candidateB ^ 2 <
      (2385436 / 1000000 : ℝ) ^ 2 :=
    (sq_lt_sq₀ (by linarith) (by norm_num)).2 hDhi
  have hXeq : sharedEndpointX * D candidateB =
      D candidateB ^ 2 - 2 - Real.sqrt 3 * F candidateB := by
    unfold sharedEndpointX
    field_simp [ne_of_gt hDpos]
    ring
  have hXlo' : (3 / 5 : ℝ) * D candidateB <
      D candidateB ^ 2 - 2 - Real.sqrt 3 * F candidateB := by
    norm_num at hGFhi ⊢
    nlinarith [hDlo, hDsqlo, hGFhi]
  have hXhi' : D candidateB ^ 2 - 2 - Real.sqrt 3 * F candidateB <
      (6031 / 10000 : ℝ) * D candidateB := by
    norm_num at hGFlo ⊢
    nlinarith [hDhi, hDsquarehi, hGFlo]
  have hXlo : (3 / 5 : ℝ) < sharedEndpointX := by
    exact (mul_lt_mul_iff_of_pos_right hDpos).1 (by
      rw [hXeq]
      exact hXlo')
  have hXhi : sharedEndpointX < 6031 / 10000 := by
    exact (mul_lt_mul_iff_of_pos_right hDpos).1 (by
      rw [hXeq]
      exact hXhi')
  have hYeq : sharedEndpointY * D candidateB =
      2 * Real.sqrt 3 - F candidateB := by
    unfold sharedEndpointY
    field_simp [ne_of_gt hDpos]
  have hYlo' : (9071 / 10000 : ℝ) * D candidateB <
      2 * Real.sqrt 3 - F candidateB := by
    nlinarith [hDhi, hglo, hFhi]
  have hYhi' : 2 * Real.sqrt 3 - F candidateB <
      (9072 / 10000 : ℝ) * D candidateB := by
    nlinarith [hDlo, hghi, hFlo]
  have hYlo : (9071 / 10000 : ℝ) < sharedEndpointY := by
    exact (mul_lt_mul_iff_of_pos_right hDpos).1 (by
      rw [hYeq]
      exact hYlo')
  have hYhi : sharedEndpointY < 9072 / 10000 := by
    exact (mul_lt_mul_iff_of_pos_right hDpos).1 (by
      rw [hYeq]
      exact hYhi')
  have hRnon : 0 ≤ sharedEndpointR := Real.sqrt_nonneg _
  have hRsq : sharedEndpointR ^ 2 =
      sharedEndpointX ^ 2 + sharedEndpointY ^ 2 := by
    unfold sharedEndpointR
    exact Real.sq_sqrt (by positivity)
  have hxySq : sharedEndpointX ^ 2 + sharedEndpointY ^ 2 <
      (109 / 100 : ℝ) ^ 2 := by
    have hXs := (sq_lt_sq₀ (by linarith [hXlo])
      (by norm_num)).2 hXhi
    have hYs := (sq_lt_sq₀ (by linarith [hYlo])
      (by norm_num)).2 hYhi
    norm_num at hXs hYs ⊢
    nlinarith
  have hRhi : sharedEndpointR < 109 / 100 := by
    by_contra hnot
    have hge : (109 / 100 : ℝ) ≤ sharedEndpointR := le_of_not_gt hnot
    have hprod : 0 ≤ (sharedEndpointR - 109 / 100) *
        (sharedEndpointR + 109 / 100) :=
      mul_nonneg (sub_nonneg.mpr hge)
        (add_nonneg hRnon (show 0 ≤ (109 / 100 : ℝ) by norm_num))
    nlinarith [hRsq, hxySq]
  exact ⟨hXlo, hXhi, hYlo, hYhi, hRhi⟩

private theorem shared_endpoint_angle_domain :
    0 < sharedEndpointKappa ∧
      sharedEndpointKappa < Real.pi / 2 ∧
      0 < sharedEndpointLowDelta ∧
      sharedEndpointLowDelta < sharedEndpointKappa := by
  obtain ⟨hDlo, hDhi, _, _⟩ := shared_endpoint_scalar_boxes
  have hDpos : 0 < D candidateB := by linarith
  have hq0 : 0 < 2 / D candidateB := by positivity
  have hq1 : 2 / D candidateB < 1 := by
    apply (div_lt_iff₀ hDpos).2
    linarith
  have hk0 : 0 < sharedEndpointKappa := by
    unfold sharedEndpointKappa
    exact Real.arccos_pos.mpr hq1
  have hkhalf : sharedEndpointKappa < Real.pi / 2 := by
    unfold sharedEndpointKappa
    have hlt := Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ 0)
      hq0 hq1.le
    rw [Real.arccos_zero] at hlt
    exact hlt
  have hhalf : (1 / 2 : ℝ) < 2 / D candidateB := by
    apply (lt_div_iff₀ hDpos).2
    linarith
  have hkthird : sharedEndpointKappa < Real.pi / 3 := by
    unfold sharedEndpointKappa
    have hlt := Real.arccos_lt_arccos
      (by norm_num : (-1 : ℝ) ≤ (1 / 2 : ℝ)) hhalf hq1.le
    have harccos : Real.arccos (1 / 2 : ℝ) = Real.pi / 3 := by
      rw [← Real.cos_pi_div_three]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
    rw [harccos] at hlt
    exact hlt
  have hfourover : 2 / D candidateB < Real.sqrt 3 / 2 := by
    apply (div_lt_iff₀ hDpos).2
    have hglo : (173205 / 100000 : ℝ) < Real.sqrt 3 := by
      have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hn := Real.sqrt_nonneg 3
      nlinarith
    have hprod : (173205 / 100000 : ℝ) *
        (2385429 / 1000000 : ℝ) < Real.sqrt 3 * D candidateB := by
      calc
        (173205 / 100000 : ℝ) * (2385429 / 1000000 : ℝ) <
            Real.sqrt 3 * (2385429 / 1000000 : ℝ) :=
          mul_lt_mul_of_pos_right hglo (by norm_num)
        _ < Real.sqrt 3 * D candidateB :=
          mul_lt_mul_of_pos_left hDlo (by positivity)
    nlinarith [hprod]
  have hkSixth : Real.pi / 6 < sharedEndpointKappa := by
    unfold sharedEndpointKappa
    have hs3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hcoshi : Real.sqrt 3 / 2 ≤ (1 : ℝ) := by nlinarith
    have hlt := Real.arccos_lt_arccos
      (by linarith [hq0]) hfourover hcoshi
    have harccos : Real.arccos (Real.sqrt 3 / 2) = Real.pi / 6 := by
      rw [← Real.cos_pi_div_six]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
    rw [harccos] at hlt
    exact hlt
  have hlpos : 0 < sharedEndpointLowDelta := by
    dsimp [sharedEndpointLowDelta]
    linarith [hkthird]
  have hlowhigh : sharedEndpointLowDelta < sharedEndpointKappa := by
    dsimp [sharedEndpointLowDelta]
    linarith [hkSixth]
  exact ⟨hk0, hkhalf, hlpos, hlowhigh⟩

private theorem shared_endpoint_kappa_cos :
    Real.cos sharedEndpointKappa = 2 / D candidateB := by
  unfold sharedEndpointKappa
  obtain ⟨hDlo, _, _, _⟩ := shared_endpoint_scalar_boxes
  have hDpos : 0 < D candidateB := by linarith
  have hqpos : 0 < 2 / D candidateB := div_pos (by norm_num) hDpos
  have hq0 : (-1 : ℝ) ≤ 2 / D candidateB := by linarith
  have hq1 : 2 / D candidateB ≤ 1 := by
    apply (div_le_iff₀ hDpos).2
    linarith
  exact Real.cos_arccos hq0 hq1

private theorem shared_endpoint_kappa_sin :
    Real.sin sharedEndpointKappa = F candidateB / D candidateB := by
  have ⟨hDlo, _, hFlo, _⟩ := shared_endpoint_scalar_boxes
  have hDpos : 0 < D candidateB := by linarith
  have hFpos : 0 < F candidateB := by linarith
  have hFsq : F candidateB ^ 2 = D candidateB ^ 2 - 4 := by
    unfold F
    have hrad : 0 ≤ D candidateB ^ 2 - 4 := by nlinarith
    exact Real.sq_sqrt hrad
  have hradid : 1 - (2 / D candidateB) ^ 2 =
      (F candidateB / D candidateB) ^ 2 := by
    field_simp [ne_of_gt hDpos]
    nlinarith [hFsq]
  have hradnon : 0 ≤ 1 - (2 / D candidateB) ^ 2 := by
    rw [hradid]
    positivity
  have hsqrt : Real.sqrt (1 - (2 / D candidateB) ^ 2) =
      F candidateB / D candidateB := by
    apply (Real.sqrt_eq_iff_mul_self_eq hradnon
      (by positivity : 0 ≤ F candidateB / D candidateB)).2
    nlinarith [hradid]
  unfold sharedEndpointKappa
  rw [Real.sin_arccos, hsqrt]

private theorem shared_endpoint_low_trig :
    Real.cos sharedEndpointLowDelta =
        (2 + Real.sqrt 3 * F candidateB) / (2 * D candidateB) ∧
      Real.sin sharedEndpointLowDelta =
        (2 * Real.sqrt 3 - F candidateB) / (2 * D candidateB) := by
  have hcos := shared_endpoint_kappa_cos
  have hsin := shared_endpoint_kappa_sin
  constructor
  · unfold sharedEndpointLowDelta
    rw [Real.cos_sub, Real.cos_pi_div_three, hcos,
      Real.sin_pi_div_three, hsin]
    ring
  · unfold sharedEndpointLowDelta
    rw [Real.sin_sub, Real.sin_pi_div_three, hcos,
      Real.cos_pi_div_three, hsin]
    ring

private theorem shared_endpoint_offsets_as_arctan :
    sharedOffset (D candidateB) sharedEndpointLowDelta =
        Real.arctan (sharedEndpointY / sharedEndpointX) ∧
      sharedOffset (D candidateB) sharedEndpointKappa =
        Real.arctan (2 / F candidateB) := by
  obtain ⟨hDlo, _, hFlo, _⟩ := shared_endpoint_scalar_boxes
  obtain ⟨hXlo, _, hYlo, _, _⟩ := shared_endpoint_coordinate_boxes
  have hDpos : 0 < D candidateB := by linarith
  have hFpos : 0 < F candidateB := by linarith
  have hXpos : 0 < sharedEndpointX := by linarith
  have hFsq : F candidateB ^ 2 = D candidateB ^ 2 - 4 := by
    unfold F
    have hrad : 0 ≤ D candidateB ^ 2 - 4 := by nlinarith
    exact Real.sq_sqrt hrad
  have hlowtrig := shared_endpoint_low_trig
  have hlowNum : 2 * Real.sin sharedEndpointLowDelta =
      sharedEndpointY := by
    rw [hlowtrig.2]
    unfold sharedEndpointY
    ring
  have hlowDen : D candidateB - 2 *
      Real.cos sharedEndpointLowDelta = sharedEndpointX := by
    rw [hlowtrig.1]
    unfold sharedEndpointX
    ring
  have hhighRatio :
      (2 * Real.sin sharedEndpointKappa) /
        (D candidateB - 2 * Real.cos sharedEndpointKappa) =
      2 / F candidateB := by
    rw [shared_endpoint_kappa_sin, shared_endpoint_kappa_cos]
    have hden : D candidateB - 4 / D candidateB =
        F candidateB ^ 2 / D candidateB := by
      field_simp [ne_of_gt hDpos]
      nlinarith [hFsq]
    have hden' : D candidateB - 2 * (2 / D candidateB) =
        F candidateB ^ 2 / D candidateB := by
      calc
        D candidateB - 2 * (2 / D candidateB) =
            D candidateB - 4 / D candidateB := by ring
        _ = _ := hden
    rw [hden']
    field_simp [ne_of_gt hDpos, ne_of_gt hFpos]
    <;> ring
  constructor
  · unfold sharedOffset
    rw [hlowNum, hlowDen]
  · unfold sharedOffset
    rw [hhighRatio]

private theorem cos_arctan_add_formula (x y : ℝ) :
    Real.cos (Real.arctan x + Real.arctan y) =
      (1 - x * y) /
        (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) := by
  rw [Real.cos_add, Real.cos_arctan, Real.sin_arctan,
    Real.cos_arctan, Real.sin_arctan]
  have hx : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hy : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp [ne_of_gt hx, ne_of_gt hy]

private theorem shared_endpoint_angle_cos :
    Real.cos (Real.arctan (sharedEndpointY / sharedEndpointX) +
      Real.arctan (2 / F candidateB)) =
      (sharedEndpointX * F candidateB - 2 * sharedEndpointY) /
        (sharedEndpointR * D candidateB) := by
  obtain ⟨hXlo, _, hYlo, _, hRhi⟩ := shared_endpoint_coordinate_boxes
  obtain ⟨hDlo, hDhi, hFlo, _⟩ := shared_endpoint_scalar_boxes
  have hXpos : 0 < sharedEndpointX := by linarith
  have hYpos : 0 < sharedEndpointY := by linarith
  have hFpos : 0 < F candidateB := by linarith
  have hDpos : 0 < D candidateB := by linarith
  have hRpos : 0 < sharedEndpointR := by
    unfold sharedEndpointR
    apply Real.sqrt_pos.mpr
    positivity
  have hRsq : sharedEndpointR ^ 2 =
      sharedEndpointX ^ 2 + sharedEndpointY ^ 2 := by
    unfold sharedEndpointR
    exact Real.sq_sqrt (by positivity)
  have hFsq : F candidateB ^ 2 = D candidateB ^ 2 - 4 := by
    unfold F
    have hrad : 0 ≤ D candidateB ^ 2 - 4 := by nlinarith
    exact Real.sq_sqrt hrad
  have hDsq : D candidateB ^ 2 = F candidateB ^ 2 + 4 := by
    nlinarith [hFsq]
  have hsqrtX : Real.sqrt (1 +
      (sharedEndpointY / sharedEndpointX) ^ 2) =
      sharedEndpointR / sharedEndpointX := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity)
      (by positivity : 0 ≤ sharedEndpointR / sharedEndpointX)).2
    have h := hRsq
    field_simp [ne_of_gt hXpos]
    nlinarith [h]
  have hsqrtF : Real.sqrt (1 + (2 / F candidateB) ^ 2) =
      D candidateB / F candidateB := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity)
      (by positivity : 0 ≤ D candidateB / F candidateB)).2
    field_simp [ne_of_gt hFpos]
    nlinarith [hDsq]
  rw [cos_arctan_add_formula, hsqrtX, hsqrtF]
  field_simp [ne_of_gt hXpos, ne_of_gt hFpos,
    ne_of_gt hRpos, ne_of_gt hDpos]

private theorem sin_le_fifth_taylor {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let g : ℝ → ℝ := fun t => Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24
  let f : ℝ → ℝ := fun t => Real.sin t - t + t ^ 3 / 6 - t ^ 5 / 120
  have hgderiv (t : ℝ) : deriv g t = -Real.sin t + t - t ^ 3 / 6 := by
    simp (disch := fun_prop) [g]
    ring
  have hganti : AntitoneOn g (Set.Icc 0 x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 x)
    · exact (by fun_prop : ContinuousOn g (Set.Icc 0 x))
    · exact (by fun_prop : DifferentiableOn ℝ g (interior (Set.Icc 0 x)))
    · intro t ht
      rw [interior_Icc] at ht
      rw [hgderiv]
      have hs := Real.sin_ge_sub_cube (le_of_lt ht.1)
      nlinarith
  have hg0 : g 0 = 0 := by simp [g]
  have hgle (t : ℝ) (ht : t ∈ Set.Icc 0 x) : g t ≤ 0 := by
    have h := hganti (show (0 : ℝ) ∈ Set.Icc 0 x from ⟨le_rfl, hx⟩)
      ht ht.1
    simpa [hg0] using h
  have hfderiv (t : ℝ) : deriv f t = g t := by
    simp (disch := fun_prop) [f, g]
    ring
  have hfanti : AntitoneOn f (Set.Icc 0 x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 x)
    · exact (by fun_prop : ContinuousOn f (Set.Icc 0 x))
    · exact (by fun_prop : DifferentiableOn ℝ f (interior (Set.Icc 0 x)))
    · intro t ht
      rw [interior_Icc] at ht
      rw [hfderiv]
      exact hgle t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hf := hfanti (show (0 : ℝ) ∈ Set.Icc 0 x from ⟨le_rfl, hx⟩)
    ⟨hx, le_rfl⟩ hx
  simp [f] at hf
  linarith

private theorem cos_gt_of_half_interval_120
    (θ l u c : ℝ)
    (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hl0 : 0 ≤ l) (hlx : l ≤ θ / 2)
    (hxu : θ / 2 ≤ u) (hu1 : u ≤ 1)
    (hcert : c < 1 - 2 *
      (u - l ^ 3 / 6 + u ^ 5 / 120) ^ 2) :
    c < Real.cos θ := by
  let x := θ / 2
  let U := u - l ^ 3 / 6 + u ^ 5 / 120
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hx3 : l ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hl0 hlx 3
  have hx5 : x ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ hx0 hxu 5
  have hsinupper : Real.sin x ≤ U := by
    have h := sin_le_fifth_taylor hx0
    dsimp [U, x] at *
    nlinarith [h, hx3, hx5]
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0
      (by linarith [Real.pi_gt_three])
  have hU0 : 0 ≤ U := le_trans hsin0 hsinupper
  have hsq : Real.sin x ^ 2 ≤ U ^ 2 := by
    nlinarith [mul_nonneg hsin0 (sub_nonneg.mpr hsinupper),
      mul_nonneg hU0 (sub_nonneg.mpr hsinupper)]
  have hcosid : Real.cos θ = 1 - 2 * Real.sin x ^ 2 := by
    have htwo := Real.cos_two_mul x
    have hsumsq := Real.sin_sq_add_cos_sq x
    have hdouble : 2 * x = θ := by dsimp [x]; ring
    rw [hdouble] at htwo
    nlinarith
  rw [hcosid]
  dsimp [U] at hsq hcert
  linarith

private theorem cos_1133pi_div_1800_gt_neg_39616_div_100000 :
    (-39616 / 100000 : ℝ) < Real.cos (1133 * Real.pi / 1800) := by
  let l : ℝ := 1133 * (3141592 / 1000000) / 3600
  let u : ℝ := 1133 * (3141593 / 1000000) / 3600
  have hθ0 : (0 : ℝ) ≤ 1133 * Real.pi / 1800 := by positivity
  have hθ2 : 1133 * Real.pi / 1800 ≤ 2 := by
    nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (1133 * Real.pi / 1800) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (1133 * Real.pi / 1800) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval_120 _ l u _ hθ0 hθ2 hl0 hlx hxu hu1
    (by dsimp [l, u]; norm_num)

theorem shared_endpoint_offset_sum_gt :
    1133 * Real.pi / 1800 < sharedEndpointAngle := by
  obtain ⟨hXlo, hXhi, hYlo, hYhi, hRhi⟩ :=
    shared_endpoint_coordinate_boxes
  obtain ⟨hDlo, hDhi, hFlo, hFhi⟩ := shared_endpoint_scalar_boxes
  have hXpos : 0 < sharedEndpointX := by linarith
  have hYpos : 0 < sharedEndpointY := by linarith
  have hFpos : 0 < F candidateB := by linarith
  have hDpos : 0 < D candidateB := by linarith
  have hRpos : 0 < sharedEndpointR := by
    unfold sharedEndpointR
    apply Real.sqrt_pos.mpr
    positivity
  have hxf : sharedEndpointX * F candidateB <
      (6031 / 10000 : ℝ) * (130013 / 100000 : ℝ) := by
    have h₁ := mul_lt_mul_of_pos_right hXhi hFpos
    have h₂ := mul_lt_mul_of_pos_left hFhi
      (by norm_num : (0 : ℝ) < 6031 / 10000)
    exact h₁.trans h₂
  have hrd : sharedEndpointR * D candidateB <
      (109 / 100 : ℝ) * (2385436 / 1000000 : ℝ) := by
    have h₁ := mul_lt_mul_of_pos_right hRhi hDpos
    have h₂ := mul_lt_mul_of_pos_left hDhi
      (by norm_num : (0 : ℝ) < 109 / 100)
    exact h₁.trans h₂
  have hcoeff : (39616 / 100000 : ℝ) *
      (sharedEndpointR * D candidateB) <
      (39616 / 100000 : ℝ) * ((109 / 100 : ℝ) *
        (2385436 / 1000000 : ℝ)) :=
    mul_lt_mul_of_pos_left hrd (by norm_num)
  have hnumerator : sharedEndpointX * F candidateB -
      2 * sharedEndpointY + (39616 / 100000 : ℝ) *
        (sharedEndpointR * D candidateB) < 0 := by
    norm_num at hxf hcoeff ⊢
    nlinarith [hYlo]
  have hcosEndpoint : Real.cos sharedEndpointAngle <
      -39616 / 100000 := by
    have hcos := shared_endpoint_angle_cos
    have hoffsets := shared_endpoint_offsets_as_arctan
    unfold sharedEndpointAngle
    rw [hoffsets.1, hoffsets.2, hcos]
    apply (div_lt_iff₀ (mul_pos hRpos hDpos)).2
    nlinarith [hnumerator]
  have hcosThreshold := cos_1133pi_div_1800_gt_neg_39616_div_100000
  have hthresholdNonneg : 0 ≤ 1133 * Real.pi / 1800 := by positivity
  have hthresholdLePi : 1133 * Real.pi / 1800 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hangleNonneg : 0 ≤ sharedEndpointAngle := by
    have hoffsets := shared_endpoint_offsets_as_arctan
    unfold sharedEndpointAngle
    rw [hoffsets.1, hoffsets.2]
    apply add_nonneg
    · exact Real.arctan_nonneg.mpr (div_nonneg (by linarith [hYlo])
        (by linarith [hXlo]))
    · exact Real.arctan_nonneg.mpr (div_nonneg (by norm_num)
        (by linarith [hFlo]))
  have hangleLtPi : sharedEndpointAngle < Real.pi := by
    have hoffsets := shared_endpoint_offsets_as_arctan
    unfold sharedEndpointAngle
    rw [hoffsets.1, hoffsets.2]
    have h₁ := Real.arctan_lt_pi_div_two (sharedEndpointY / sharedEndpointX)
    have h₂ := Real.arctan_lt_pi_div_two (2 / F candidateB)
    linarith [Real.pi_pos]
  by_contra hnot
  have hle : sharedEndpointAngle ≤ 1133 * Real.pi / 1800 :=
    le_of_not_gt hnot
  by_cases heq : sharedEndpointAngle = 1133 * Real.pi / 1800
  · rw [heq] at hcosEndpoint
    linarith
  · have hlt : sharedEndpointAngle < 1133 * Real.pi / 1800 :=
      lt_of_le_of_ne hle heq
    have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi
      hangleNonneg hthresholdLePi hlt
    linarith

private theorem sharedOffset_hasDeriv (s δ : ℝ) (hs : 2 < s) :
    HasDerivAt (sharedOffset s) (sharedOffsetDerivative s δ) δ := by
  have hdenpos : 0 < s - 2 * Real.cos δ := by
    nlinarith [Real.cos_le_one δ]
  have hnum : HasDerivAt (fun t : ℝ => 2 * Real.sin t)
      (2 * Real.cos δ) δ := by
    convert (Real.hasDerivAt_sin δ).const_mul 2 using 1 <;> ring
  have hden : HasDerivAt (fun t : ℝ => s - 2 * Real.cos t)
      (2 * Real.sin δ) δ := by
    convert (Real.hasDerivAt_cos δ).const_mul (-2) |>.const_add s using 1
    · funext t; ring
    · ring
  have hdiv := HasDerivAt.div hnum hden hdenpos.ne'
  have hquot : HasDerivAt
      (fun t : ℝ => 2 * Real.sin t / (s - 2 * Real.cos t))
      ((2 * Real.cos δ * (s - 2 * Real.cos δ) -
        2 * Real.sin δ * (2 * Real.sin δ)) /
        (s - 2 * Real.cos δ) ^ 2) δ := hdiv
  have hcomp := (Real.hasDerivAt_arctan _).comp δ hquot
  have htrig := Real.sin_sq_add_cos_sq δ
  have hdenid : (s - 2 * Real.cos δ) ^ 2 +
      4 * Real.sin δ ^ 2 = s ^ 2 + 4 - 4 * s * Real.cos δ := by
    nlinarith [htrig]
  have hnumid : 2 * Real.cos δ * (s - 2 * Real.cos δ) -
      2 * Real.sin δ * (2 * Real.sin δ) =
      2 * (s * Real.cos δ - 2) := by
    nlinarith [htrig]
  have hQpos : 0 < s ^ 2 + 4 - 4 * s * Real.cos δ := by
    rw [← hdenid]
    positivity
  have hden2pos : 0 < (s - 2 * Real.cos δ) ^ 2 +
      4 * Real.sin δ ^ 2 := by positivity
  have hquotEq :
      1 / (1 + (2 * Real.sin δ / (s - 2 * Real.cos δ)) ^ 2) *
        ((2 * Real.cos δ * (s - 2 * Real.cos δ) -
          2 * Real.sin δ * (2 * Real.sin δ)) /
          (s - 2 * Real.cos δ) ^ 2) =
      2 * (s * Real.cos δ - 2) /
        (s ^ 2 + 4 - 4 * s * Real.cos δ) := by
    rw [hnumid]
    calc
      1 / (1 + (2 * Real.sin δ / (s - 2 * Real.cos δ)) ^ 2) *
          (2 * (s * Real.cos δ - 2) / (s - 2 * Real.cos δ) ^ 2) =
        2 * (s * Real.cos δ - 2) /
          ((s - 2 * Real.cos δ) ^ 2 + 4 * Real.sin δ ^ 2) := by
            field_simp [ne_of_gt hdenpos, ne_of_gt hden2pos]
            ring
      _ = _ := by rw [hdenid]
  convert hcomp using 1
  · rfl
  · exact hquotEq.symm

private theorem sharedOffsetDerivative_hasDeriv (s δ : ℝ) (hs : 2 < s) :
    HasDerivAt (sharedOffsetDerivative s)
      (sharedOffsetSecondDerivative s δ) δ := by
  let num : ℝ → ℝ := fun t => 2 * (s * Real.cos t - 2)
  let den : ℝ → ℝ := fun t => s ^ 2 + 4 - 4 * s * Real.cos t
  have hnum : HasDerivAt num (-2 * s * Real.sin δ) δ := by
    have h := ((Real.hasDerivAt_cos δ).const_mul s).const_mul 2
    have h' := h.const_add (-4)
    convert h' using 1
    · funext t; ring
    · ring
  have hden : HasDerivAt den (4 * s * Real.sin δ) δ := by
    convert (Real.hasDerivAt_cos δ).const_mul (-4 * s) |>.const_add
      (s ^ 2 + 4) using 1
    · funext t; ring
    · ring
  have hdenpos : 0 < den δ := by
    dsimp [den]
    have hcos := Real.cos_le_one δ
    have hspos : 0 < s := by linarith
    have hprod : 0 ≤ 4 * s * (1 - Real.cos δ) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hcos)
    have hsq : 0 < (s - 2) ^ 2 := sq_pos_of_pos (by linarith)
    have hid : s ^ 2 + 4 - 4 * s * Real.cos δ =
        (s - 2) ^ 2 + 4 * s * (1 - Real.cos δ) := by ring
    rw [hid]
    exact add_pos_of_pos_of_nonneg hsq hprod
  have hdiv := HasDerivAt.div hnum hden hdenpos.ne'
  have hQpos : 0 < s ^ 2 + 4 - 4 * s * Real.cos δ := by
    simpa [den] using hdenpos
  have hquotEq :
      ((-2 * s * Real.sin δ * (s ^ 2 + 4 - 4 * s * Real.cos δ) -
        2 * (s * Real.cos δ - 2) * (4 * s * Real.sin δ)) /
        (s ^ 2 + 4 - 4 * s * Real.cos δ) ^ 2) =
      -2 * s * (s ^ 2 - 4) * Real.sin δ /
        (s ^ 2 + 4 - 4 * s * Real.cos δ) ^ 2 := by
    field_simp [ne_of_gt hQpos]
    ring
  change HasDerivAt (num / den)
    (sharedOffsetSecondDerivative s δ) δ
  convert hdiv using 1
  simpa [sharedOffsetSecondDerivative, num, den] using hquotEq.symm

private theorem sharedOffset_second (s δ : ℝ) (hs : 2 < s) :
    deriv^[2] (sharedOffset s) δ = sharedOffsetSecondDerivative s δ := by
  have hfun : deriv (sharedOffset s) = sharedOffsetDerivative s := by
    funext t
    exact (sharedOffset_hasDeriv s t hs).deriv
  have hGfun : deriv (sharedOffsetDerivative s) =
      sharedOffsetSecondDerivative s := by
    funext t
    exact (sharedOffsetDerivative_hasDeriv s t hs).deriv
  rw [Function.iterate_succ_apply, Function.iterate_one, hfun]
  exact congrFun hGfun δ

theorem sharedOffset_strictConcaveOn_Icc
    (s l u : ℝ) (hs : 2 < s) (hl : 0 < l) (hu : u < Real.pi) :
    StrictConcaveOn ℝ (Set.Icc l u) (sharedOffset s) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Icc l u)
  · intro δ hδ
    exact (sharedOffset_hasDeriv s δ hs).continuousAt.continuousWithinAt
  · intro δ hδ
    rw [sharedOffset_second s δ hs]
    have hδ0 : 0 < δ := lt_of_lt_of_le hl hδ.1
    have hδpi : δ < Real.pi := lt_of_le_of_lt hδ.2 hu
    have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 hδpi
    have hsq : 0 < s ^ 2 - 4 := by nlinarith
    have hq : 0 < s ^ 2 + 4 - 4 * s * Real.cos δ := by
      have hcos := Real.cos_le_one δ
      have hprod : 0 ≤ 4 * s * (1 - Real.cos δ) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hcos)
      have hspos : 0 < s := by linarith
      have hbase : 0 < (s - 2) ^ 2 := sq_pos_of_pos (by linarith)
      have hid : s ^ 2 + 4 - 4 * s * Real.cos δ =
          (s - 2) ^ 2 + 4 * s * (1 - Real.cos δ) := by ring
      rw [hid]
      exact add_pos_of_pos_of_nonneg hbase hprod
    have hnum : -2 * s * (s ^ 2 - 4) * Real.sin δ < 0 := by
      have : 0 < 2 * s * (s ^ 2 - 4) * Real.sin δ := by positivity
      linarith
    exact div_neg_of_neg_of_pos hnum (sq_pos_of_pos hq)

theorem sharedOffset_strictMonoOn_Icc
    (s l u : ℝ) (hs : 2 < s) (hl : 0 < l) (hlu : l < u)
    (hu : u = Real.arccos (2 / s)) :
    StrictMonoOn (sharedOffset s) (Set.Icc l u) := by
  have hcont : ContinuousOn (sharedOffset s) (Set.Icc l u) := by
    intro δ hδ
    exact (sharedOffset_hasDeriv s δ hs).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Icc l u) hcont
  intro δ hδ
  rw [interior_Icc] at hδ
  have hδ0 : 0 ≤ δ := le_of_lt (lt_trans hl hδ.1)
  have hu0 : 0 ≤ 2 / s := by positivity
  have hu1 : 2 / s ≤ 1 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < s)).2
    linarith
  have huPi : u ≤ Real.pi := by rw [hu]; exact Real.arccos_le_pi _
  have hcosu : Real.cos u = 2 / s := by
    rw [hu]
    exact Real.cos_arccos (by linarith) hu1
  have hcoslt : Real.cos u < Real.cos δ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hδ0 huPi hδ.2
  have hmul : s * Real.cos u < s * Real.cos δ :=
    (mul_lt_mul_iff_of_pos_left (by linarith : 0 < s)).2 hcoslt
  rw [hcosu] at hmul
  have htop : 0 < s * Real.cos δ - 2 := by
    have hcancel : s * (2 / s) = 2 := by field_simp
    rw [hcancel] at hmul
    linarith
  have hq : 0 < s ^ 2 + 4 - 4 * s * Real.cos δ := by
    have hcos := Real.cos_le_one δ
    have hprod : 0 ≤ 4 * s * (1 - Real.cos δ) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hcos)
    have hbase : 0 < (s - 2) ^ 2 := sq_pos_of_pos (by linarith)
    have hid : s ^ 2 + 4 - 4 * s * Real.cos δ =
        (s - 2) ^ 2 + 4 * s * (1 - Real.cos δ) := by ring
    rw [hid]
    exact add_pos_of_pos_of_nonneg hbase hprod
  rw [(sharedOffset_hasDeriv s δ hs).deriv]
  exact div_pos (by nlinarith) hq

theorem sharedOffset_pair_ge_endpoint
    (s l u x y : ℝ)
    (hconc : ConcaveOn ℝ (Set.Icc l u) (sharedOffset s))
    (hmono : StrictMonoOn (sharedOffset s) (Set.Icc l u))
    (hlu : l < u)
    (hx : x ∈ Set.Icc l u) (hy : y ∈ Set.Icc l u)
    (hxy : l + u ≤ x + y) :
    sharedOffset s l + sharedOffset s u ≤
      sharedOffset s x + sharedOffset s y := by
  have hchord (z : ℝ) (hz : z ∈ Set.Icc l u) :
      (u - l) * sharedOffset s z ≥
        (u - z) * sharedOffset s l + (z - l) * sharedOffset s u := by
    let a : ℝ := (u - z) / (u - l)
    let b : ℝ := (z - l) / (u - l)
    have ha : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (sub_nonneg.mpr hz.2) (sub_nonneg.mpr hlu.le)
    have hb : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hlu.le)
    have hab : a + b = 1 := by
      dsimp [a, b]
      have hden : u - l ≠ 0 := ne_of_gt (sub_pos.mpr hlu)
      field_simp
      ring
    have hcombine : a * l + b * u = z := by
      dsimp [a, b]
      have hden : u - l ≠ 0 := ne_of_gt (sub_pos.mpr hlu)
      field_simp
      ring
    have hconcave := hconc.2 (show l ∈ Set.Icc l u from ⟨le_rfl, hlu.le⟩)
      (show u ∈ Set.Icc l u from ⟨hlu.le, le_rfl⟩) ha hb hab
    have hconcave' : a * sharedOffset s l + b * sharedOffset s u ≤
        sharedOffset s z := by
      simpa only [smul_eq_mul, hcombine] using hconcave
    dsimp [a, b] at hconcave'
    have hmul := mul_le_mul_of_nonneg_right hconcave'
      (sub_nonneg.mpr hlu.le)
    have hden : u - l ≠ 0 := ne_of_gt (sub_pos.mpr hlu)
    have hmul' : (u - l) *
        ((u - z) / (u - l) * sharedOffset s l +
          (z - l) / (u - l) * sharedOffset s u) ≤
        (u - l) * sharedOffset s z := by
      nlinarith [hmul]
    have hcancel : (u - l) *
        ((u - z) / (u - l) * sharedOffset s l +
          (z - l) / (u - l) * sharedOffset s u) =
        (u - z) * sharedOffset s l + (z - l) * sharedOffset s u := by
      field_simp [hden]
    rw [hcancel] at hmul'
    exact hmul'
  have hends : sharedOffset s l < sharedOffset s u :=
    hmono (show l ∈ Set.Icc l u from ⟨le_rfl, hlu.le⟩)
      (show u ∈ Set.Icc l u from ⟨hlu.le, le_rfl⟩) hlu
  have hsum : 0 ≤ x + y - l - u := by linarith
  have hprod := mul_nonneg hsum (sub_nonneg.mpr hends.le)
  have hc₁ := hchord x hx
  have hc₂ := hchord y hy
  nlinarith

theorem sharedOffset_nonincreasing_radius
    (s S δ : ℝ) (hs : 2 < s) (hS : s ≤ S)
    (hδ0 : 0 ≤ δ) (hδpi : δ ≤ Real.pi) (hS2 : 2 < S) :
    sharedOffset S δ ≤ sharedOffset s δ := by
  have hsden : 0 < s - 2 * Real.cos δ := by
    nlinarith [Real.cos_le_one δ]
  have hSden : 0 < S - 2 * Real.cos δ := by
    nlinarith [Real.cos_le_one δ]
  have hsin : 0 ≤ 2 * Real.sin δ := by
    have hsin' := Real.sin_nonneg_of_nonneg_of_le_pi hδ0 hδpi
    positivity
  have hdenle : s - 2 * Real.cos δ ≤ S - 2 * Real.cos δ := by linarith
  have hquot : 2 * Real.sin δ / (S - 2 * Real.cos δ) ≤
      2 * Real.sin δ / (s - 2 * Real.cos δ) := by
    rw [div_le_div_iff₀ hSden hsden]
    nlinarith [mul_nonneg hsin (sub_nonneg.mpr hdenle)]
  exact (Real.arctan_le_arctan_iff).2 hquot

theorem sharedOffset_sum_gt_candidate_endpoint
    (s δ₁ δ₂ : ℝ)
    (hs : 2 < s) (hsD : s ≤ D candidateB)
    (hδ₁ : sharedEndpointLowDelta ≤ δ₁ ∧
      δ₁ ≤ sharedEndpointKappa)
    (hδ₂ : sharedEndpointLowDelta ≤ δ₂ ∧
      δ₂ ≤ sharedEndpointKappa)
    (hspread : Real.pi / 3 ≤ δ₁ + δ₂) :
    1133 * Real.pi / 1800 <
      sharedOffset s δ₁ + sharedOffset s δ₂ := by
  obtain ⟨hκpos, hκhalf, hlpos, hlκ⟩ :=
    shared_endpoint_angle_domain
  obtain ⟨hDlo, _, _, _⟩ := shared_endpoint_scalar_boxes
  have hDgt : 2 < D candidateB := by linarith
  have hκpi : sharedEndpointKappa < Real.pi := by linarith
  have hu : sharedEndpointKappa = Real.arccos (2 / D candidateB) := rfl
  have hconcStrict := sharedOffset_strictConcaveOn_Icc
    (D candidateB) sharedEndpointLowDelta sharedEndpointKappa
    hDgt hlpos hκpi
  have hmono := sharedOffset_strictMonoOn_Icc
    (D candidateB) sharedEndpointLowDelta sharedEndpointKappa
    hDgt hlpos hlκ hu
  have hpair := sharedOffset_pair_ge_endpoint
    (D candidateB) sharedEndpointLowDelta sharedEndpointKappa δ₁ δ₂
    hconcStrict.concaveOn hmono hlκ
    ⟨hδ₁.1, hδ₁.2⟩ ⟨hδ₂.1, hδ₂.2⟩ (by
      dsimp [sharedEndpointLowDelta]
      linarith [hspread])
  have hδ₁0 : 0 ≤ δ₁ := le_trans (le_of_lt hlpos) hδ₁.1
  have hδ₂0 : 0 ≤ δ₂ := le_trans (le_of_lt hlpos) hδ₂.1
  have hδ₁pi : δ₁ ≤ Real.pi := hδ₁.2.trans (le_of_lt hκpi)
  have hδ₂pi : δ₂ ≤ Real.pi := hδ₂.2.trans (le_of_lt hκpi)
  have hmonoRadius₁ := sharedOffset_nonincreasing_radius
    s (D candidateB) δ₁ hs hsD hδ₁0 hδ₁pi hDgt
  have hmonoRadius₂ := sharedOffset_nonincreasing_radius
    s (D candidateB) δ₂ hs hsD hδ₂0 hδ₂pi hDgt
  have hendpoint := shared_endpoint_offset_sum_gt
  have hendpoint' : 1133 * Real.pi / 1800 <
      sharedOffset (D candidateB) sharedEndpointLowDelta +
        sharedOffset (D candidateB) sharedEndpointKappa := by
    simpa [sharedEndpointAngle] using hendpoint
  linarith

theorem sharedOffset_sum_gt_candidate_endpoint_of_support
    (s δ₁ δ₂ : ℝ)
    (hs : 2 < s) (hsD : s ≤ D candidateB)
    (hδ₁κ : δ₁ ≤ Real.arccos (2 / s))
    (hδ₂κ : δ₂ ≤ Real.arccos (2 / s))
    (hspread : Real.pi / 3 ≤ δ₁ + δ₂) :
    1133 * Real.pi / 1800 <
      sharedOffset s δ₁ + sharedOffset s δ₂ := by
  obtain ⟨hκpos, hκhalf, hlpos, hlκ⟩ :=
    shared_endpoint_angle_domain
  obtain ⟨hDlo, hDhi, _, _⟩ := shared_endpoint_scalar_boxes
  have hDpos : 0 < D candidateB := by linarith
  have hspos : 0 < s := by linarith
  have hratio : 2 / D candidateB ≤ 2 / s := by
    apply (div_le_div_iff₀ hDpos hspos).2
    nlinarith [hsD]
  have hratioD : 2 / D candidateB ≤ 1 := by
    apply (div_le_iff₀ hDpos).2
    linarith
  have hratios : 2 / s ≤ 1 := by
    apply (div_le_iff₀ hspos).2
    linarith
  have hkappa : Real.arccos (2 / s) ≤ sharedEndpointKappa := by
    by_cases heq : 2 / D candidateB = 2 / s
    · rw [← heq]
      rfl
    · have hlt : 2 / D candidateB < 2 / s := lt_of_le_of_ne hratio heq
      have hratioDnonneg : 0 ≤ 2 / D candidateB := by positivity
      have hlt' := Real.arccos_lt_arccos
        (by linarith [hratioDnonneg]) hlt hratios
      exact hlt'.le
  have hδ₁lo : sharedEndpointLowDelta ≤ δ₁ := by
    dsimp [sharedEndpointLowDelta]
    linarith [hspread, hδ₂κ.trans hkappa]
  have hδ₂lo : sharedEndpointLowDelta ≤ δ₂ := by
    dsimp [sharedEndpointLowDelta]
    linarith [hspread, hδ₁κ.trans hkappa]
  exact sharedOffset_sum_gt_candidate_endpoint s δ₁ δ₂ hs hsD
    ⟨hδ₁lo, hδ₁κ.trans hkappa⟩
    ⟨hδ₂lo, hδ₂κ.trans hkappa⟩ hspread

end CP15
