import CP15.ActualInnerCycle

namespace CP15

set_option maxHeartbeats 0

open scoped InnerProductSpace

def candidateOuterStartIndex (i : Fin 5) : Fin 15 :=
  match i.val with
  | 0 => 7
  | 1 => 14
  | 2 => 11
  | 3 => 2
  | 4 => 1
  | _ => 0

def candidateOuterEndIndex (i : Fin 5) : Fin 15 :=
  match i.val with
  | 0 => 12
  | 1 => 13
  | 2 => 6
  | 3 => 0
  | 4 => 3
  | _ => 0

theorem candidate_outer_start_cycle_step (i : Fin 5) :
    Candidate.point (candidateOuterStartIndex (i + 1)) =
      candidateRotate72 (Candidate.point (candidateOuterStartIndex i)) := by
  have hts : Candidate.t * Candidate.s = 1 / 2 := by
    unfold Candidate.t
    field_simp [ne_of_gt Candidate.s_pos]
  have hvt : Candidate.v * Candidate.t = Candidate.t - Candidate.s := by
    have h : Candidate.t * (1 - Candidate.v) = Candidate.s := by
      calc
        Candidate.t * (1 - Candidate.v) =
            Candidate.t * (2 * Candidate.s ^ 2) := by
          rw [← Candidate.two_s_sq]
        _ = (Candidate.t * Candidate.s) * (2 * Candidate.s) := by ring
        _ = Candidate.s := by rw [hts]; ring
    nlinarith [h]
  have hut : Candidate.u * Candidate.t = Candidate.v + 1 / 2 := by
    rw [Candidate.t_linear]
    nlinarith [Candidate.s_u_v, Candidate.u_sq_v]
  have hus : Candidate.u * Candidate.s = Candidate.v + 1 / 4 := by
    simpa [mul_comm] using Candidate.s_u_v
  have huc : 2 * Candidate.u * Candidate.c = Candidate.s + Candidate.u := by
    calc
      2 * Candidate.u * Candidate.c = 2 * Candidate.c * Candidate.u := by ring
      _ = Candidate.s + Candidate.u := Candidate.two_c_u
  have hvc : 4 * Candidate.c * Candidate.v = 1 := Candidate.four_c_v
  have huv : 2 * Candidate.u * Candidate.v = Candidate.s :=
    Candidate.two_u_v
  fin_cases i <;>
    simp [candidateOuterStartIndex, candidateRotate72, Candidate.point,
      Candidate.pt] <;>
    constructor <;>
    nlinarith [Candidate.two_s_c, Candidate.two_s_v,
      Candidate.two_c_u, Candidate.two_u_v, Candidate.c_sub_v,
      Candidate.t_linear, Candidate.s_sq, Candidate.c_sq,
      Candidate.u_sq, Candidate.v_sq, Candidate.pentagon_identity,
      hus, huc, hvc, huv, hvt, hut]

theorem candidate_outer_end_cycle_step (i : Fin 5) :
    Candidate.point (candidateOuterEndIndex (i + 1)) =
      candidateRotate72 (Candidate.point (candidateOuterEndIndex i)) := by
  have hts : Candidate.t * Candidate.s = 1 / 2 := by
    unfold Candidate.t
    field_simp [ne_of_gt Candidate.s_pos]
  have hvt : Candidate.v * Candidate.t = Candidate.t - Candidate.s := by
    have h : Candidate.t * (1 - Candidate.v) = Candidate.s := by
      calc
        Candidate.t * (1 - Candidate.v) =
            Candidate.t * (2 * Candidate.s ^ 2) := by
          rw [← Candidate.two_s_sq]
        _ = (Candidate.t * Candidate.s) * (2 * Candidate.s) := by ring
        _ = Candidate.s := by rw [hts]; ring
    nlinarith [h]
  have hut : Candidate.u * Candidate.t = Candidate.v + 1 / 2 := by
    rw [Candidate.t_linear]
    nlinarith [Candidate.s_u_v, Candidate.u_sq_v]
  have hus : Candidate.u * Candidate.s = Candidate.v + 1 / 4 := by
    simpa [mul_comm] using Candidate.s_u_v
  have huc : 2 * Candidate.u * Candidate.c = Candidate.s + Candidate.u := by
    calc
      2 * Candidate.u * Candidate.c = 2 * Candidate.c * Candidate.u := by ring
      _ = Candidate.s + Candidate.u := Candidate.two_c_u
  have hvc : 4 * Candidate.c * Candidate.v = 1 := Candidate.four_c_v
  have huv : 2 * Candidate.u * Candidate.v = Candidate.s :=
    Candidate.two_u_v
  fin_cases i <;>
    simp [candidateOuterEndIndex, candidateRotate72, Candidate.point,
      Candidate.pt] <;>
    constructor <;>
    nlinarith [Candidate.two_s_c, Candidate.two_s_v,
      Candidate.two_c_u, Candidate.two_u_v, Candidate.c_sub_v,
      Candidate.t_linear, Candidate.s_sq, Candidate.c_sq,
      Candidate.u_sq, Candidate.v_sq, Candidate.pentagon_identity,
      hus, huc, hvc, huv, hvt, hut]

theorem candidate_contact_factor_minus :
    ((candidateB / candidateInnerRadius : ℂ) *
      ((Real.cos (contactAngle candidateB candidateInnerRadius) : ℂ) -
        Real.sin (contactAngle candidateB candidateInnerRadius) * Complex.I)) =
      ⟨1 + 2 * Candidate.c * Candidate.s, -2 * Candidate.s ^ 2⟩ := by
  have hsr : candidateInnerRadius * Candidate.s = 1 := by
    unfold candidateInnerRadius
    field_simp [ne_of_gt Candidate.s_pos]
  have hreal : candidateInnerRadius + 2 * Candidate.c =
      candidateInnerRadius * (1 + 2 * Candidate.c * Candidate.s) := by
    calc
      candidateInnerRadius + 2 * Candidate.c =
      candidateInnerRadius +
            2 * Candidate.c * (candidateInnerRadius * Candidate.s) := by
        rw [hsr]
        ring
      _ = candidateInnerRadius *
          (1 + 2 * Candidate.c * Candidate.s) := by ring
  have himag : Candidate.s = candidateInnerRadius * Candidate.s ^ 2 := by
    calc
      Candidate.s = (candidateInnerRadius * Candidate.s) * Candidate.s := by
        rw [hsr]
        ring
      _ = candidateInnerRadius * Candidate.s ^ 2 := by ring
  rw [candidate_contact_angle_cos_sin.1,
    candidate_contact_angle_cos_sin.2]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    field_simp [ne_of_gt candidateB_pos,
      ne_of_gt candidateInnerRadius_pos]
    rw [← hreal]
  · simp [Complex.mul_re, Complex.mul_im]
    field_simp [ne_of_gt candidateB_pos,
      ne_of_gt candidateInnerRadius_pos]
    rw [← himag]

theorem candidate_contact_factor_plus :
    ((candidateB / candidateInnerRadius : ℂ) *
      ((Real.cos (contactAngle candidateB candidateInnerRadius) : ℂ) +
        Real.sin (contactAngle candidateB candidateInnerRadius) * Complex.I)) =
      ⟨1 + 2 * Candidate.c * Candidate.s, 2 * Candidate.s ^ 2⟩ := by
  have hsr : candidateInnerRadius * Candidate.s = 1 := by
    unfold candidateInnerRadius
    field_simp [ne_of_gt Candidate.s_pos]
  have hreal : candidateInnerRadius + 2 * Candidate.c =
      candidateInnerRadius * (1 + 2 * Candidate.c * Candidate.s) := by
    calc
      candidateInnerRadius + 2 * Candidate.c =
          candidateInnerRadius +
            2 * Candidate.c * (candidateInnerRadius * Candidate.s) := by
        rw [hsr]
        ring
      _ = candidateInnerRadius *
          (1 + 2 * Candidate.c * Candidate.s) := by ring
  have himag : Candidate.s = candidateInnerRadius * Candidate.s ^ 2 := by
    calc
      Candidate.s = (candidateInnerRadius * Candidate.s) * Candidate.s := by
        rw [hsr]
        ring
      _ = candidateInnerRadius * Candidate.s ^ 2 := by ring
  rw [candidate_contact_angle_cos_sin.1,
    candidate_contact_angle_cos_sin.2]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    field_simp [ne_of_gt candidateB_pos,
      ne_of_gt candidateInnerRadius_pos]
    rw [← hreal]
  · simp [Complex.mul_re, Complex.mul_im]
    field_simp [ne_of_gt candidateB_pos,
      ne_of_gt candidateInnerRadius_pos]
    nlinarith [himag]

theorem candidate_outer_start_contact_base :
    planeComplex (Candidate.pointAtSeparationTwo
      (candidateOuterStartIndex 0)) =
      (⟨1 + 2 * Candidate.c * Candidate.s, -2 * Candidate.s ^ 2⟩ : ℂ) *
        planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex 0)) := by
  rw [show candidateOuterStartIndex 0 = 7 by rfl,
    show candidateInnerCycleIndex 0 = 9 by rfl]
  change planeComplex ((2 : ℝ) • Candidate.point 7) =
    (⟨1 + 2 * Candidate.c * Candidate.s, -2 * Candidate.s ^ 2⟩ : ℂ) *
      planeComplex ((2 : ℝ) • Candidate.point 9)
  rw [planeComplex_real_smul_two, planeComplex_real_smul_two]
  have h7 : Candidate.point (7 : Fin 15) =
      Candidate.pt (1 / 2 + Candidate.u + Candidate.v)
        (Candidate.t - Candidate.s - Candidate.v) := by rfl
  have h9 : Candidate.point (9 : Fin 15) =
      Candidate.pt Candidate.c (Candidate.t - Candidate.s) := by rfl
  have ht : Candidate.t * Candidate.s = 1 / 2 := by
    unfold Candidate.t
    field_simp [ne_of_gt Candidate.s_pos]
  have hcs : 2 * Candidate.c ^ 2 * Candidate.s =
      Candidate.c * Candidate.u := by
    calc
      2 * Candidate.c ^ 2 * Candidate.s =
          Candidate.c * (2 * Candidate.s * Candidate.c) := by ring
      _ = Candidate.c * Candidate.u := by rw [Candidate.two_s_c]
  have hcpart : 4 * Candidate.c ^ 2 * Candidate.s =
      Candidate.s + Candidate.u := by
    calc
      4 * Candidate.c ^ 2 * Candidate.s =
          2 * (Candidate.c * Candidate.u) := by
        calc
          4 * Candidate.c ^ 2 * Candidate.s =
              2 * (2 * Candidate.c ^ 2 * Candidate.s) := by ring
          _ = 2 * (Candidate.c * Candidate.u) := by rw [hcs]
      _ = Candidate.s + Candidate.u := by
        calc
          2 * (Candidate.c * Candidate.u) =
              2 * Candidate.c * Candidate.u := by ring
          _ = Candidate.s + Candidate.u := Candidate.two_c_u
  have hspart : 4 * Candidate.s ^ 3 = 3 * Candidate.s - Candidate.u := by
    calc
      4 * Candidate.s ^ 3 =
          2 * Candidate.s * (2 * Candidate.s ^ 2) := by ring
      _ = 2 * Candidate.s * (1 - Candidate.v) := by
          rw [Candidate.two_s_sq]
      _ = 2 * Candidate.s - (Candidate.u - Candidate.s) := by
          calc
            2 * Candidate.s * (1 - Candidate.v) =
            2 * Candidate.s - 2 * Candidate.s * Candidate.v := by ring
            _ = 2 * Candidate.s - (Candidate.u - Candidate.s) := by
              rw [Candidate.two_s_v]
      _ = 3 * Candidate.s - Candidate.u := by ring
  have hts : Candidate.s * Candidate.t = 1 / 2 := by
    simpa [mul_comm] using ht
  have hst : 4 * Candidate.s ^ 2 * (Candidate.t - Candidate.s) =
      2 * Candidate.s - 4 * Candidate.s ^ 3 := by
    calc
      4 * Candidate.s ^ 2 * (Candidate.t - Candidate.s) =
          4 * Candidate.s * (Candidate.s * Candidate.t) -
            4 * Candidate.s ^ 3 := by ring
      _ = 4 * Candidate.s * (1 / 2) - 4 * Candidate.s ^ 3 := by rw [hts]
      _ = 2 * Candidate.s - 4 * Candidate.s ^ 3 := by ring
  have hreal : 1 + 2 * Candidate.u + 2 * Candidate.v =
      (1 + 2 * Candidate.c * Candidate.s) * (2 * Candidate.c) +
        4 * Candidate.s ^ 2 * (Candidate.t - Candidate.s) := by
    calc
      1 + 2 * Candidate.u + 2 * Candidate.v =
          2 * Candidate.c + 2 * Candidate.u := by
        nlinarith [Candidate.c_sub_v]
      _ = 2 * Candidate.c + (Candidate.s + Candidate.u) +
          2 * Candidate.s - (3 * Candidate.s - Candidate.u) := by ring
      _ = 2 * Candidate.c + 4 * Candidate.c ^ 2 * Candidate.s +
          2 * Candidate.s - 4 * Candidate.s ^ 3 := by
        rw [← hcpart, ← hspart]
      _ = (1 + 2 * Candidate.c * Candidate.s) *
          (2 * Candidate.c) +
          2 * Candidate.s - 4 * Candidate.s ^ 3 := by ring
      _ = (1 + 2 * Candidate.c * Candidate.s) *
          (2 * Candidate.c) +
          4 * Candidate.s ^ 2 * (Candidate.t - Candidate.s) := by
        rw [hst]
        ring
  have himag : 2 * (Candidate.t - Candidate.s - Candidate.v) =
      (1 + 2 * Candidate.c * Candidate.s) *
          (2 * (Candidate.t - Candidate.s)) -
        4 * Candidate.s ^ 2 * Candidate.c := by
    have hrel : 2 * Candidate.c * Candidate.s *
        (Candidate.t - 2 * Candidate.s) = -Candidate.v := by
      calc
        2 * Candidate.c * Candidate.s *
            (Candidate.t - 2 * Candidate.s) =
            2 * Candidate.c * (Candidate.s * Candidate.t) -
              2 * Candidate.c * (2 * Candidate.s ^ 2) := by ring
        _ = Candidate.c - 2 * Candidate.c * (1 - Candidate.v) := by
          rw [hts, Candidate.two_s_sq]
          ring
        _ = 2 * Candidate.c * Candidate.v - Candidate.c := by ring
        _ = -Candidate.v := by
          have hcv : 2 * Candidate.c * Candidate.v = 1 / 2 := by
            nlinarith [Candidate.four_c_v]
          linarith [Candidate.c_sub_v]
    have hrel4 : 4 * Candidate.c * Candidate.s *
        (Candidate.t - 2 * Candidate.s) = -2 * Candidate.v := by
      calc
        4 * Candidate.c * Candidate.s *
            (Candidate.t - 2 * Candidate.s) =
            2 * (2 * Candidate.c * Candidate.s *
              (Candidate.t - 2 * Candidate.s)) := by ring
        _ = 2 * (-Candidate.v) := by rw [hrel]
        _ = -2 * Candidate.v := by ring
    calc
      2 * (Candidate.t - Candidate.s - Candidate.v) =
          2 * (Candidate.t - Candidate.s) - 2 * Candidate.v := by ring
      _ = 2 * (Candidate.t - Candidate.s) +
          4 * Candidate.c * Candidate.s *
            (Candidate.t - 2 * Candidate.s) := by rw [hrel4]; ring
      _ = (1 + 2 * Candidate.c * Candidate.s) *
            (2 * (Candidate.t - Candidate.s)) -
          4 * Candidate.s ^ 2 * Candidate.c := by ring
  rw [h7, h9]
  apply Complex.ext
  · simp [planeComplex, Candidate.pt, Complex.mul_re,
      Complex.mul_im]
    nlinarith [hreal]
  · simp [planeComplex, Candidate.pt, Complex.mul_re,
      Complex.mul_im]
    nlinarith [himag]

theorem candidate_outer_end_contact_base :
    planeComplex (Candidate.pointAtSeparationTwo
      (candidateOuterEndIndex 0)) =
      (⟨1 + 2 * Candidate.c * Candidate.s, 2 * Candidate.s ^ 2⟩ : ℂ) *
        planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex 0)) := by
  rw [show candidateOuterEndIndex 0 = 12 by rfl,
    show candidateInnerCycleIndex 0 = 9 by rfl]
  change planeComplex ((2 : ℝ) • Candidate.point 12) =
    (⟨1 + 2 * Candidate.c * Candidate.s, 2 * Candidate.s ^ 2⟩ : ℂ) *
      planeComplex ((2 : ℝ) • Candidate.point 9)
  rw [planeComplex_real_smul_two, planeComplex_real_smul_two]
  have h12 : Candidate.point (12 : Fin 15) =
      Candidate.pt (Candidate.c + Candidate.s)
        (Candidate.t - Candidate.s + Candidate.c) := by rfl
  have h9 : Candidate.point (9 : Fin 15) =
      Candidate.pt Candidate.c (Candidate.t - Candidate.s) := by rfl
  have ht : Candidate.t * Candidate.s = 1 / 2 := by
    unfold Candidate.t
    field_simp [ne_of_gt Candidate.s_pos]
  have hts : Candidate.s * Candidate.t = 1 / 2 := by
    simpa [mul_comm] using ht
  have hreal : 2 * (Candidate.c + Candidate.s) =
      (1 + 2 * Candidate.c * Candidate.s) * (2 * Candidate.c) -
        4 * Candidate.s ^ 2 * (Candidate.t - Candidate.s) := by
    have hcpart : 4 * Candidate.c ^ 2 * Candidate.s =
        Candidate.s + Candidate.u := by
      have hcs : 2 * Candidate.c ^ 2 * Candidate.s =
          Candidate.c * Candidate.u := by
        calc
          2 * Candidate.c ^ 2 * Candidate.s =
              Candidate.c * (2 * Candidate.s * Candidate.c) := by ring
          _ = Candidate.c * Candidate.u := by rw [Candidate.two_s_c]
      calc
        4 * Candidate.c ^ 2 * Candidate.s =
            2 * (2 * Candidate.c ^ 2 * Candidate.s) := by ring
        _ = 2 * (Candidate.c * Candidate.u) := by
          rw [hcs]
        _ = 2 * Candidate.c * Candidate.u := by ring
        _ = Candidate.s + Candidate.u := Candidate.two_c_u
    have hspart : 4 * Candidate.s ^ 3 =
        3 * Candidate.s - Candidate.u := by
      calc
        4 * Candidate.s ^ 3 =
            2 * Candidate.s * (2 * Candidate.s ^ 2) := by ring
        _ = 2 * Candidate.s * (1 - Candidate.v) := by
          rw [Candidate.two_s_sq]
        _ = 2 * Candidate.s - 2 * Candidate.s * Candidate.v := by ring
        _ = 2 * Candidate.s - (Candidate.u - Candidate.s) := by
          rw [Candidate.two_s_v]
        _ = 3 * Candidate.s - Candidate.u := by ring
    have hst : 4 * Candidate.s ^ 2 * (Candidate.t - Candidate.s) =
        2 * Candidate.s - 4 * Candidate.s ^ 3 := by
      calc
        4 * Candidate.s ^ 2 * (Candidate.t - Candidate.s) =
            4 * Candidate.s * (Candidate.s * Candidate.t) -
              4 * Candidate.s ^ 3 := by ring
        _ = 4 * Candidate.s * (1 / 2) -
              4 * Candidate.s ^ 3 := by rw [hts]
        _ = 2 * Candidate.s - 4 * Candidate.s ^ 3 := by ring
    calc
      2 * (Candidate.c + Candidate.s) =
          2 * Candidate.c + 2 * Candidate.s := by ring
      _ = 2 * Candidate.c + (Candidate.s + Candidate.u) -
          2 * Candidate.s + (3 * Candidate.s - Candidate.u) := by ring
      _ = 2 * Candidate.c + 4 * Candidate.c ^ 2 * Candidate.s -
          2 * Candidate.s + 4 * Candidate.s ^ 3 := by
        rw [← hcpart, ← hspart]
      _ = 2 * Candidate.c + 4 * Candidate.c ^ 2 * Candidate.s -
          (2 * Candidate.s - 4 * Candidate.s ^ 3) := by ring
      _ = (1 + 2 * Candidate.c * Candidate.s) *
          (2 * Candidate.c) -
          4 * Candidate.s ^ 2 * (Candidate.t - Candidate.s) := by
        rw [hst]
        ring
  have himag : 2 * (Candidate.t - Candidate.s + Candidate.c) =
      (1 + 2 * Candidate.c * Candidate.s) *
          (2 * (Candidate.t - Candidate.s)) +
        4 * Candidate.s ^ 2 * Candidate.c := by
    have hct : 4 * Candidate.c * Candidate.s * Candidate.t =
        2 * Candidate.c := by
      calc
        4 * Candidate.c * Candidate.s * Candidate.t =
            4 * Candidate.c * (Candidate.s * Candidate.t) := by ring
        _ = 4 * Candidate.c * (1 / 2) := by rw [hts]
        _ = 2 * Candidate.c := by ring
    calc
      2 * (Candidate.t - Candidate.s + Candidate.c) =
          2 * (Candidate.t - Candidate.s) + 2 * Candidate.c := by ring
      _ = 2 * (Candidate.t - Candidate.s) +
          4 * Candidate.c * Candidate.s * Candidate.t := by rw [← hct]
      _ = (1 + 2 * Candidate.c * Candidate.s) *
          (2 * (Candidate.t - Candidate.s)) +
          4 * Candidate.s ^ 2 * Candidate.c := by ring
  rw [h12, h9]
  apply Complex.ext
  · simp [planeComplex, Candidate.pt, Complex.mul_re,
      Complex.mul_im]
    nlinarith [hreal, hts]
  · simp [planeComplex, Candidate.pt, Complex.mul_re,
      Complex.mul_im]
    nlinarith [himag, hts]

noncomputable def candidateContactFactorMinus : ℂ :=
  ⟨1 + 2 * Candidate.c * Candidate.s, -2 * Candidate.s ^ 2⟩

noncomputable def candidateContactFactorPlus : ℂ :=
  ⟨1 + 2 * Candidate.c * Candidate.s, 2 * Candidate.s ^ 2⟩

theorem planeComplex_candidate_scaled_cycle
    (idx : Fin 5 → Fin 15)
    (hstep : ∀ i, Candidate.point (idx (i + 1)) =
      candidateRotate72 (Candidate.point (idx i))) :
    ∀ i, planeComplex (Candidate.pointAtSeparationTwo (idx (i + 1))) =
      ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
        planeComplex (Candidate.pointAtSeparationTwo (idx i)) := by
  intro i
  calc
    planeComplex (Candidate.pointAtSeparationTwo (idx (i + 1))) =
        (2 : ℂ) * planeComplex (Candidate.point (idx (i + 1))) := by
      change planeComplex ((2 : ℝ) • Candidate.point (idx (i + 1))) = _
      exact planeComplex_real_smul_two _
    _ = (2 : ℂ) * planeComplex
        (candidateRotate72 (Candidate.point (idx i))) := by rw [hstep i]
    _ = (2 : ℂ) * (((Candidate.v : ℂ) + Candidate.u * Complex.I) *
        planeComplex (Candidate.point (idx i))) := by
      rw [planeComplex_candidateRotate72]
    _ = ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
        planeComplex (Candidate.pointAtSeparationTwo (idx i)) := by
      change (2 : ℂ) * (((Candidate.v : ℂ) + Candidate.u * Complex.I) *
          planeComplex (Candidate.point (idx i))) =
        ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
          planeComplex ((2 : ℝ) • Candidate.point (idx i))
      rw [planeComplex_real_smul_two]
      ring

theorem candidate_contact_formula_of_base
    (idx : Fin 5 → Fin 15) (d : ℂ)
    (hbase : planeComplex (Candidate.pointAtSeparationTwo (idx 0)) =
      d * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 0)))
    (houter : ∀ i, planeComplex (Candidate.pointAtSeparationTwo
        (idx (i + 1))) =
      ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
        planeComplex (Candidate.pointAtSeparationTwo (idx i)))
    (hinner : ∀ i, planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex (i + 1))) =
      ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
        planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex i))) :
    ∀ i, planeComplex (Candidate.pointAtSeparationTwo (idx i)) =
      d * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex i)) := by
  have h1 : planeComplex (Candidate.pointAtSeparationTwo (idx 1)) =
      d * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 1)) := by
    have hi : planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 1)) =
        ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
          planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 0)) := by simpa using hinner 0
    rw [hi]
    calc
      planeComplex (Candidate.pointAtSeparationTwo (idx 1)) =
          ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            planeComplex (Candidate.pointAtSeparationTwo (idx 0)) := by
        simpa using houter (0 : Fin 5)
      _ = ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            (d * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 0))) := by rw [hbase]
      _ = d * (((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 0))) := by ring
  have h2 : planeComplex (Candidate.pointAtSeparationTwo (idx 2)) =
      d * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 2)) := by
    have hi : planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 2)) =
        ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
          planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 1)) := by simpa using hinner 1
    rw [hi]
    calc
      planeComplex (Candidate.pointAtSeparationTwo (idx 2)) =
          ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            planeComplex (Candidate.pointAtSeparationTwo (idx 1)) := by
        simpa using houter (1 : Fin 5)
      _ = ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            (d * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 1))) := by rw [h1]
      _ = d * (((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 1))) := by ring
  have h3 : planeComplex (Candidate.pointAtSeparationTwo (idx 3)) =
      d * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 3)) := by
    have hi : planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 3)) =
        ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
          planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 2)) := by simpa using hinner 2
    rw [hi]
    calc
      planeComplex (Candidate.pointAtSeparationTwo (idx 3)) =
          ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            planeComplex (Candidate.pointAtSeparationTwo (idx 2)) := by
        simpa using houter (2 : Fin 5)
      _ = ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            (d * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 2))) := by rw [h2]
      _ = d * (((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 2))) := by ring
  have h4 : planeComplex (Candidate.pointAtSeparationTwo (idx 4)) =
      d * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 4)) := by
    have hi : planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 4)) =
        ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
          planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 3)) := by simpa using hinner 3
    rw [hi]
    calc
      planeComplex (Candidate.pointAtSeparationTwo (idx 4)) =
          ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            planeComplex (Candidate.pointAtSeparationTwo (idx 3)) := by
        simpa using houter (3 : Fin 5)
      _ = ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            (d * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 3))) := by rw [h3]
      _ = d * (((Candidate.v : ℂ) + Candidate.u * Complex.I) *
            planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 3))) := by ring
  intro i
  fin_cases i
  · exact hbase
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem candidate_outer_start_contact_formula (i : Fin 5) :
    planeComplex (Candidate.pointAtSeparationTwo
      (candidateOuterStartIndex i)) =
      candidateContactFactorMinus * planeComplex
        (Candidate.pointAtSeparationTwo (candidateInnerCycleIndex i)) := by
  apply candidate_contact_formula_of_base candidateOuterStartIndex
    candidateContactFactorMinus
    (by simpa [candidateContactFactorMinus] using
      candidate_outer_start_contact_base)
    (planeComplex_candidate_scaled_cycle candidateOuterStartIndex
      candidate_outer_start_cycle_step)
    (planeComplex_candidate_scaled_cycle candidateInnerCycleIndex
      candidate_inner_cycle_step)
    i

theorem candidate_outer_end_contact_formula (i : Fin 5) :
    planeComplex (Candidate.pointAtSeparationTwo
      (candidateOuterEndIndex i)) =
      candidateContactFactorPlus * planeComplex
        (Candidate.pointAtSeparationTwo (candidateInnerCycleIndex i)) := by
  apply candidate_contact_formula_of_base candidateOuterEndIndex
    candidateContactFactorPlus
    (by simpa [candidateContactFactorPlus] using
      candidate_outer_end_contact_base)
    (planeComplex_candidate_scaled_cycle candidateOuterEndIndex
      candidate_outer_end_cycle_step)
    (planeComplex_candidate_scaled_cycle candidateInnerCycleIndex
      candidate_inner_cycle_step)
    i

end CP15
