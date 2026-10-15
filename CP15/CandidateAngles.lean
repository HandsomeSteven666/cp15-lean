import CP15.LocalDerivativeBounds
import CP15.BasicAngleBounds

namespace CP15

noncomputable def candidateInnerRadius : ℝ := 1 / Candidate.s

theorem candidate_sin_pi_div_five : Real.sin (Real.pi / 5) = Candidate.s := by
  have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi / 5 by positivity) (show Real.pi / 5 ≤ Real.pi by linarith [Real.pi_pos])
  have hsc := Real.sin_sq_add_cos_sq (Real.pi / 5)
  have hc : Real.cos (Real.pi / 5) = Candidate.c := by
    simpa [Candidate.c, Candidate.root5] using Real.cos_pi_div_five
  rw [hc] at hsc
  apply (sq_eq_sq₀ hsin0 Candidate.s_pos.le).mp
  linarith [Candidate.pentagon_identity]

theorem candidateInnerRadius_eq_inv_sin :
    candidateInnerRadius = 1 / Real.sin (Real.pi / 5) := by
  rw [candidate_sin_pi_div_five]
  rfl

theorem candidateInnerRadius_pos : 0 < candidateInnerRadius := by
  unfold candidateInnerRadius
  positivity [Candidate.s_pos]

theorem candidateInnerRadius_local_bounds :
    (1697 / 1000 : ℝ) < candidateInnerRadius ∧ candidateInnerRadius < 853 / 500 := by
  have hsquare : candidateInnerRadius ^ 2 = 2 + 2 / Candidate.root5 := by
    unfold candidateInnerRadius
    rw [div_pow, one_pow]
    exact Candidate.inv_s_sq
  have hlo : (8 / 9 : ℝ) < 2 / Candidate.root5 := by
    apply (lt_div_iff₀ Candidate.root5_pos).2
    nlinarith [Candidate.root5_tight_bounds.2]
  have hhi : 2 / Candidate.root5 < (200 / 223 : ℝ) := by
    apply (div_lt_iff₀ Candidate.root5_pos).2
    nlinarith [Candidate.root5_tight_bounds.1]
  constructor <;> nlinarith [candidateInnerRadius_pos]

theorem candidateB_local_bounds :
    (35213 / 10000 : ℝ) < candidateB ∧ candidateB < 35214 / 10000 := by
  have hrootup : Candidate.root5 < (223607 / 100000 : ℝ) := by
    nlinarith [Candidate.root5_sq, Candidate.root5_pos]
  have hratio : (559 / 625 : ℝ) < 2 / Candidate.root5 := by
    apply (lt_div_iff₀ Candidate.root5_pos).2
    nlinarith
  have hrad : 0 ≤ 1 + 2 / Candidate.root5 := by positivity [Candidate.root5_pos]
  have hsqrt : (13763 / 10000 : ℝ) < Real.sqrt (1 + 2 / Candidate.root5) := by
    nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (1 + 2 / Candidate.root5)]
  have hBsq : candidateB ^ 2 =
      6 + 2 / Candidate.root5 + 4 * Real.sqrt (1 + 2 / Candidate.root5) := by
    rw [← Candidate.two_rho_eq_candidateB]
    exact Candidate.two_rho_sq
  constructor
  · nlinarith [candidateB_pos]
  · linarith [Candidate.candidateB_lt_352136_div_100000]

/-- The defining candidate radius is exactly the hypotenuse obtained
from an inner pentagon vertex and its two outer contacts. -/
theorem candidateB_inner_contact_identity :
    candidateB ^ 2 = candidateInnerRadius ^ 2 +
      4 * Candidate.c * candidateInnerRadius + 4 := by
  have ht : Candidate.t = candidateInnerRadius / 2 := by
    unfold Candidate.t candidateInnerRadius
    ring
  rw [← Candidate.two_rho_eq_candidateB, mul_pow, Candidate.rho_sq, ht]
  nlinarith [Candidate.pentagon_identity]

theorem candidate_contactCos_identity :
    contactCos candidateB candidateInnerRadius =
      (candidateInnerRadius + 2 * Candidate.c) / candidateB := by
  have hnum : candidateB ^ 2 + candidateInnerRadius ^ 2 - 4 =
      2 * candidateInnerRadius * (candidateInnerRadius + 2 * Candidate.c) := by
    nlinarith [candidateB_inner_contact_identity]
  unfold contactCos
  rw [hnum]
  field_simp [ne_of_gt candidateB_pos, ne_of_gt candidateInnerRadius_pos]

/-- The actual inverse trigonometric contact formula has the correct
branch at the exact candidate, checked by a positive triangle radicand. -/
theorem candidate_contact_angle_cos_sin :
    Real.cos (contactAngle candidateB candidateInnerRadius) =
        (candidateInnerRadius + 2 * Candidate.c) / candidateB ∧
    Real.sin (contactAngle candidateB candidateInnerRadius) = 2 * Candidate.s / candidateB := by
  have hb := candidateB_local_bounds
  have hr := candidateInnerRadius_local_bounds
  have hbox := local_outer_derivative_bounds candidateB candidateInnerRadius
    hb.1.le hb.2.le hr.1.le hr.2.le
  have hcos2 := contactCos_sq_lt_one candidateB candidateInnerRadius
    candidateB_pos candidateInnerRadius_pos hbox.1
  have hcLo : -1 ≤ contactCos candidateB candidateInnerRadius := by nlinarith
  have hcHi : contactCos candidateB candidateInnerRadius ≤ 1 := by nlinarith
  have hc : Real.cos (contactAngle candidateB candidateInnerRadius) =
      (candidateInnerRadius + 2 * Candidate.c) / candidateB := by
    unfold contactAngle
    rw [Real.cos_arccos hcLo hcHi, candidate_contactCos_identity]
  refine ⟨hc, ?_⟩
  have hunit : ((candidateInnerRadius + 2 * Candidate.c) / candidateB) ^ 2 +
      (2 * Candidate.s / candidateB) ^ 2 = 1 := by
    field_simp [ne_of_gt candidateB_pos]
    nlinarith [candidateB_inner_contact_identity, Candidate.pentagon_identity]
  have hsc := Real.sin_sq_add_cos_sq (contactAngle candidateB candidateInnerRadius)
  rw [hc] at hsc
  have hs0 : 0 ≤ Real.sin (contactAngle candidateB candidateInnerRadius) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hrhs0 : 0 ≤ 2 * Candidate.s / candidateB := by positivity [Candidate.s_pos, candidateB_pos]
  apply (sq_eq_sq₀ hs0 hrhs0).mp
  linarith

theorem candidate_contact_angle_lt_pi_div_five :
    contactAngle candidateB candidateInnerRadius < Real.pi / 5 := by
  have hcB : Candidate.c * candidateB < (13 / 16 : ℝ) * (1761 / 500) :=
    (mul_lt_mul_of_pos_left Candidate.candidateB_lt_1761_div_500 Candidate.c_pos).trans
      (mul_lt_mul_of_pos_right Candidate.simple_bounds.2.2.2.1 (by norm_num))
  have hcomp : Candidate.c < contactCos candidateB candidateInnerRadius := by
    rw [candidate_contactCos_identity]
    apply (lt_div_iff₀ candidateB_pos).2
    nlinarith [candidateInnerRadius_local_bounds.1, Candidate.simple_bounds.2.2.1]
  have hcangle : Real.arccos Candidate.c = Real.pi / 5 := by
    have hc : Real.cos (Real.pi / 5) = Candidate.c := by
      simpa [Candidate.c, Candidate.root5] using Real.cos_pi_div_five
    rw [← hc]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  have hcoshi : contactCos candidateB candidateInnerRadius ≤ 1 := by
    have hc := candidate_contact_angle_cos_sin.1
    rw [candidate_contactCos_identity]
    rw [← hc]
    exact Real.cos_le_one _
  exact (Real.arccos_lt_arccos (by linarith [Candidate.c_pos]) hcomp hcoshi).trans_eq hcangle

/-- An exact trigonometric proof of the reference balance. It derives
`sin (pi/5 - gamma) = 1/B` and checks the arcsine branch; it does not
postulate that the candidate gaps have a particular polar ordering. -/
theorem candidate_outer_inner_angle_balance :
    outerAlpha candidateB + 2 * contactAngle candidateB candidateInnerRadius =
      2 * Real.pi / 5 := by
  have hsr : Candidate.s * candidateInnerRadius = 1 := by
    unfold candidateInnerRadius
    field_simp [ne_of_gt Candidate.s_pos]
  have hc : Real.cos (Real.pi / 5) = Candidate.c := by
    simpa [Candidate.c, Candidate.root5] using Real.cos_pi_div_five
  have hsin : Real.sin (Real.pi / 5 - contactAngle candidateB candidateInnerRadius) =
      1 / candidateB := by
    rw [Real.sin_sub, candidate_sin_pi_div_five, hc,
      candidate_contact_angle_cos_sin.1, candidate_contact_angle_cos_sin.2]
    field_simp [ne_of_gt candidateB_pos]
    nlinarith
  have hdomain : Real.pi / 5 - contactAngle candidateB candidateInnerRadius ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have hlt := candidate_contact_angle_lt_pi_div_five
    have hn : 0 ≤ contactAngle candidateB candidateInnerRadius := Real.arccos_nonneg _
    constructor <;> linarith [Real.pi_pos]
  have hasin := Real.arcsin_eq_of_sin_eq hsin hdomain
  unfold outerAlpha
  linarith

theorem candidate_inner_pair_angle :
    contactAngle candidateInnerRadius candidateInnerRadius = 2 * Real.pi / 5 := by
  have hsr2 : candidateInnerRadius ^ 2 * Candidate.s ^ 2 = 1 := by
    unfold candidateInnerRadius
    field_simp [ne_of_gt Candidate.s_pos]
  have hcos : Real.cos (2 * Real.pi / 5) = 1 - 2 * Candidate.s ^ 2 := by
    have h := Real.cos_two_mul (Real.pi / 5)
    have hc : Real.cos (Real.pi / 5) = Candidate.c := by
      simpa [Candidate.c, Candidate.root5] using Real.cos_pi_div_five
    simp only [hc, candidate_sin_pi_div_five] at h
    rw [show 2 * (Real.pi / 5) = 2 * Real.pi / 5 by ring] at h
    nlinarith [Candidate.pentagon_identity]
  have hcontact : contactCos candidateInnerRadius candidateInnerRadius =
      1 - 2 * Candidate.s ^ 2 := by
    unfold contactCos
    apply (div_eq_iff (by positivity [candidateInnerRadius_pos] :
      2 * candidateInnerRadius * candidateInnerRadius ≠ 0)).2
    nlinarith
  unfold contactAngle
  exact Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos])
    (hcontact.trans hcos.symm)

theorem candidate_angle_reference_balance :
    outerAlpha candidateB + 2 * contactAngle candidateB candidateInnerRadius =
      contactAngle candidateInnerRadius candidateInnerRadius := by
  rw [candidate_outer_inner_angle_balance, candidate_inner_pair_angle]

end CP15
