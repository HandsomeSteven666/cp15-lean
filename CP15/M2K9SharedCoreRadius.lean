import CP15.M2K9SharedForcedContacts

open scoped InnerProductSpace

namespace CP15

/-- Rank two forces the Gram determinant of three plane vectors to
vanish. This polynomial identity is the algebraic replacement for
the angle parametrization of a shared contact pair. -/
theorem plane_three_gram_identity (y x z : Plane) :
    (‖y‖ ^ 2 * ⟪x, z⟫_ℝ -
      ⟪y, x⟫_ℝ * ⟪y, z⟫_ℝ) ^ 2 =
    (‖y‖ ^ 2 * ‖x‖ ^ 2 - ⟪y, x⟫_ℝ ^ 2) *
      (‖y‖ ^ 2 * ‖z‖ ^ 2 - ⟪y, z⟫_ℝ ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private theorem shared_core_gram_polynomial_positive
    (S R Z : ℝ)
    (hSlo : (16 / 3 : ℝ) < S)
    (hShi : S ≤ (2385436 / 1000000 : ℝ) ^ 2)
    (hR0 : 0 ≤ R)
    (hRhi : R ≤ (27 / 25 : ℝ) ^ 2)
    (hZ0 : 0 ≤ Z)
    (hZhi : Z < S - 4) :
    0 < R ^ 2 - R * S - R * Z - 4 * R +
      S ^ 2 - S * Z - 4 * S + Z ^ 2 - 4 * Z + 16 := by
  let U : ℝ := (2385436 / 1000000 : ℝ) ^ 2
  let L : ℝ := (27 / 25 : ℝ) ^ 2
  have hU6 : U < 6 := by dsimp [U]; norm_num
  have hL2 : L < 2 := by dsimp [L]; norm_num
  have hRhi' : R ≤ L := hRhi
  have hShi' : S ≤ U := hShi
  have hfactor₁ : 0 ≤ (U - S) * (12 - S - U + 2 * R) := by
    apply mul_nonneg (by linarith) (by linarith)
  have hfactor₂ : 0 ≤ (L - R) * (2 * U - R - L) := by
    apply mul_nonneg (by linarith)
    have hUlo : (5 : ℝ) < U := by dsimp [U]; norm_num
    linarith
  have hcorner : 0 < (U - L) ^ 2 - 12 * U + 48 := by
    dsimp [U, L]
    norm_num
  have hP : 0 < (S - R) ^ 2 - 12 * S + 48 := by
    nlinarith [hfactor₁, hfactor₂, hcorner]
  have hfactor₃ : 0 < (R - Z + 8) * (S - Z - 4) := by
    apply mul_pos
    · linarith
    · linarith
  nlinarith [hP, hfactor₃]

private theorem shared_core_gram_impossible
    (S R Z t : ℝ)
    (hSlo : (16 / 3 : ℝ) < S)
    (hShi : S ≤ (2385436 / 1000000 : ℝ) ^ 2)
    (hR0 : 0 ≤ R) (hRhi : R ≤ (27 / 25 : ℝ) ^ 2)
    (hZ0 : 0 ≤ Z) (hZhi : Z < S - 4)
    (hsep : 4 ≤ R + Z - 2 * t)
    (hapos : 0 < (S + R - 4) / 2)
    (hbpos : 0 < (S + Z - 4) / 2)
    (hgram :
      (S * t - ((S + R - 4) / 2) * ((S + Z - 4) / 2)) ^ 2 =
      (S * R - ((S + R - 4) / 2) ^ 2) *
        (S * Z - ((S + Z - 4) / 2) ^ 2)) : False := by
  let a := (S + R - 4) / 2
  let bb := (S + Z - 4) / 2
  let C := (R + Z - 4) / 2
  let E := R ^ 2 - R * S - R * Z - 4 * R +
    S ^ 2 - S * Z - 4 * S + Z ^ 2 - 4 * Z + 16
  have hSpos : 0 < S := by linarith
  have hCneg : C < 0 := by
    dsimp [C]
    nlinarith [hShi, hRhi]
  have hT : 0 < a * bb - S * C := by
    have hmul : 0 < a * bb := mul_pos hapos hbpos
    have hneg : S * C < 0 := mul_neg_of_pos_of_neg hSpos hCneg
    linarith
  have htle : t ≤ C := by dsimp [C]; linarith
  have hTle : a * bb - S * C ≤ a * bb - S * t := by
    nlinarith [mul_nonneg hSpos.le (sub_nonneg.mpr htle)]
  have hsqle : (a * bb - S * C) ^ 2 ≤
      (a * bb - S * t) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTle)
      (add_nonneg hT.le (le_trans hT.le hTle))]
  have hEneg :
      (a * bb - S * C) ^ 2 -
        (S * R - a ^ 2) * (S * Z - bb ^ 2) ≤ 0 := by
    have hgram' : (a * bb - S * t) ^ 2 =
        (S * R - a ^ 2) * (S * Z - bb ^ 2) := by
      calc
        (a * bb - S * t) ^ 2 = (S * t - a * bb) ^ 2 := by ring
        _ = _ := hgram
    calc
      (a * bb - S * C) ^ 2 -
          (S * R - a ^ 2) * (S * Z - bb ^ 2) ≤
        (a * bb - S * t) ^ 2 -
          (S * R - a ^ 2) * (S * Z - bb ^ 2) :=
        sub_le_sub_right hsqle _
      _ = 0 := by rw [hgram']; ring
  have hident :
      (a * bb - S * C) ^ 2 -
        (S * R - a ^ 2) * (S * Z - bb ^ 2) = S * E := by
    dsimp [a, bb, C, E]
    ring
  have hEpos : 0 < E :=
    shared_core_gram_polynomial_positive S R Z
      hSlo hShi hR0 hRhi hZ0 hZhi
  have hprod := mul_pos hSpos hEpos
  linarith

/-- The two strict targets of one shared blocker each have radius above
`27/25`. The proof is entirely algebraic: the rank-two Gram identity,
the two contact equations, and separation yield a polynomial contradiction
if either target is smaller. -/
theorem strict_shared_targets_radius_gt_27_div_25
    (x z y : Plane)
    (hylo : (16 / 3 : ℝ) < ‖y‖ ^ 2)
    (hyhi : ‖y‖ ≤ 2385436 / 1000000)
    (hxy : dist x y = 2) (hzy : dist z y = 2)
    (hblockx : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ)
    (hblockz : ‖z‖ ^ 2 < ⟪y, z⟫_ℝ)
    (hxz : 2 ≤ dist x z) :
    (27 / 25 : ℝ) < ‖x‖ ∧ (27 / 25 : ℝ) < ‖z‖ := by
  have hfirst (x z : Plane)
      (hxy : dist x y = 2) (hzy : dist z y = 2)
      (hblockx : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ)
      (hblockz : ‖z‖ ^ 2 < ⟪y, z⟫_ℝ)
      (hxz : 2 ≤ dist x z) :
      (27 / 25 : ℝ) < ‖x‖ := by
    by_contra hnot
    let S := ‖y‖ ^ 2
    let R := ‖x‖ ^ 2
    let Z := ‖z‖ ^ 2
    let t := ⟪x, z⟫_ℝ
    have hRhi : R ≤ (27 / 25 : ℝ) ^ 2 := by
      have hn := norm_nonneg x
      nlinarith
    have hShi : S ≤ (2385436 / 1000000 : ℝ) ^ 2 := by
      have hn := norm_nonneg y
      nlinarith
    have hZhi : Z < S - 4 := by
      have h := strict_contact_vector_inner_lt_neg_four z y hzy hblockz
      rw [inner_sub_right, real_inner_self_eq_norm_sq] at h
      dsimp [S, Z]
      rw [real_inner_comm] at h
      nlinarith [hblockz, real_inner_comm z y]
    have hxySq : ‖x - y‖ ^ 2 = 4 := by
      rw [← dist_eq_norm, hxy]
      norm_num
    have hzySq : ‖z - y‖ ^ 2 = 4 := by
      rw [← dist_eq_norm, hzy]
      norm_num
    rw [norm_sub_sq_real] at hxySq hzySq
    have ha : ⟪y, x⟫_ℝ = (S + R - 4) / 2 := by
      dsimp [S, R]
      nlinarith [real_inner_comm x y]
    have hb : ⟪y, z⟫_ℝ = (S + Z - 4) / 2 := by
      dsimp [S, Z]
      nlinarith [real_inner_comm z y]
    have hsepSq : 4 ≤ dist x z ^ 2 := by
      nlinarith [dist_nonneg (x := x) (y := z)]
    have hsepEq : dist x z ^ 2 = R + Z - 2 * t := by
      dsimp [R, Z, t]
      rw [dist_eq_norm, norm_sub_sq_real]
      ring
    have hsep : 4 ≤ R + Z - 2 * t := by linarith
    have hgram := plane_three_gram_identity y x z
    rw [ha, hb] at hgram
    have hapos : 0 < (S + R - 4) / 2 := by
      rw [← ha]
      exact lt_of_le_of_lt (sq_nonneg ‖x‖) hblockx
    have hbpos : 0 < (S + Z - 4) / 2 := by
      rw [← hb]
      exact lt_of_le_of_lt (sq_nonneg ‖z‖) hblockz
    exact shared_core_gram_impossible S R Z t hylo hShi
      (sq_nonneg ‖x‖) hRhi (sq_nonneg ‖z‖) hZhi hsep
      hapos hbpos hgram
  have hone := hfirst x z hxy hzy hblockx hblockz hxz
  have hother := hfirst z x hzy hxy hblockz hblockx
    (by simpa only [dist_comm] using hxz)
  exact ⟨hone, hother⟩

end CP15
