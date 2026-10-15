import CP15.CandidateExact
import CP15.CandidateAngles

namespace CP15

set_option maxHeartbeats 0

open scoped InnerProductSpace

def candidateInnerCycleIndex (i : Fin 5) : Fin 15 :=
  match i.val with
  | 0 => 9
  | 1 => 10
  | 2 => 8
  | 3 => 4
  | 4 => 5
  | _ => 0

noncomputable def candidateRotate72 (x : Plane) : Plane :=
  !₂[Candidate.v * x 0 - Candidate.u * x 1,
    Candidate.u * x 0 + Candidate.v * x 1]

theorem candidate_cos_two_pi_div_five :
    Real.cos (2 * Real.pi / 5) = Candidate.v := by
  have hc : Real.cos (Real.pi / 5) = Candidate.c := by
    simpa [Candidate.c, Candidate.root5] using Real.cos_pi_div_five
  have hs : Real.sin (Real.pi / 5) = Candidate.s :=
    candidate_sin_pi_div_five
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
    Real.cos_two_mul, hc]
  rw [Candidate.two_c_sq]
  ring

theorem candidate_sin_two_pi_div_five :
    Real.sin (2 * Real.pi / 5) = Candidate.u := by
  have hc : Real.cos (Real.pi / 5) = Candidate.c := by
    simpa [Candidate.c, Candidate.root5] using Real.cos_pi_div_five
  have hs : Real.sin (Real.pi / 5) = Candidate.s :=
    candidate_sin_pi_div_five
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
    Real.sin_two_mul, hc, hs]
  exact Candidate.two_s_c

theorem planeComplex_candidateRotate72 (x : Plane) :
    planeComplex (candidateRotate72 x) =
      ((Candidate.v : ℂ) + Candidate.u * Complex.I) * planeComplex x := by
  apply Complex.ext <;>
    simp [planeComplex, candidateRotate72, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem planeComplex_eq_polar_coordinates (x : Plane) (θ : ℝ)
    (hθ : θ = polarArg x ∨ θ = polarArg x + 2 * Real.pi) :
    planeComplex x =
      ⟨‖x‖ * Real.cos θ, ‖x‖ * Real.sin θ⟩ := by
  apply Complex.ext
  · have h := Complex.norm_mul_cos_arg (planeComplex x)
    rw [planeComplex_norm] at h
    change θ = Complex.arg (planeComplex x) ∨
      θ = Complex.arg (planeComplex x) + 2 * Real.pi at hθ
    rcases hθ with hθ | hθ
    · simpa [hθ] using h.symm
    · simpa [hθ, Real.cos_add_two_pi] using h.symm
  · have h := Complex.norm_mul_sin_arg (planeComplex x)
    rw [planeComplex_norm] at h
    change θ = Complex.arg (planeComplex x) ∨
      θ = Complex.arg (planeComplex x) + 2 * Real.pi at hθ
    rcases hθ with hθ | hθ
    · simpa [hθ] using h.symm
    · simpa [hθ, Real.sin_add_two_pi] using h.symm

/-- In explicit Cartesian coordinates, the five inner centers of the
candidate follow the positive regular-pentagon rotation. -/
theorem candidate_inner_cycle_step (i : Fin 5) :
    Candidate.point (candidateInnerCycleIndex (i + 1)) =
      candidateRotate72 (Candidate.point (candidateInnerCycleIndex i)) := by
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
    simp [candidateInnerCycleIndex, candidateRotate72, Candidate.point,
      Candidate.pt] <;>
    constructor <;>
    nlinarith [Candidate.two_s_c, Candidate.two_s_v,
      Candidate.two_c_u, Candidate.two_u_v, Candidate.c_sub_v,
      Candidate.t_linear, Candidate.s_sq, Candidate.c_sq,
      Candidate.u_sq, Candidate.v_sq, Candidate.pentagon_identity,
      hus, huc, hvc, huv, hvt, hut]

theorem candidate_inner_cycle_radius (i : Fin 5) :
    ‖Candidate.pointAtSeparationTwo
      (candidateInnerCycleIndex i)‖ = candidateInnerRadius := by
  have hbase : ‖Candidate.point (candidateInnerCycleIndex i)‖ = Candidate.t := by
    have hsquare : ‖Candidate.point (candidateInnerCycleIndex i)‖ ^ 2 =
        Candidate.t ^ 2 := by
      fin_cases i <;> simp [candidateInnerCycleIndex] <;>
        first
        | exact Candidate.radius_sq_09
        | exact Candidate.radius_sq_10
        | exact Candidate.radius_sq_08
        | exact Candidate.radius_sq_04
        | exact Candidate.radius_sq_05
    nlinarith [norm_nonneg
      (Candidate.point (candidateInnerCycleIndex i)), Candidate.t_pos]
  rw [Candidate.pointAtSeparationTwo, norm_smul, hbase]
  norm_num
  unfold candidateInnerRadius Candidate.t
  field_simp [ne_of_gt Candidate.s_pos]

end CP15
