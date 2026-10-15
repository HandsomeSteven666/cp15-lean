import CP15.CandidateOuterCycle

namespace CP15

/-- The reflection recurrence for the two local displacement parameters
along one edge of the candidate pentagon. -/
noncomputable def candidateRigidityReflection (x : ℝ × ℝ) : ℝ × ℝ :=
  (Candidate.v * x.1 - Candidate.u * x.2,
    -Candidate.u * x.1 - Candidate.v * x.2)

theorem candidateRigidityReflection_involutive :
    Function.Involutive candidateRigidityReflection := by
  intro x
  rcases x with ⟨d, lam⟩
  have hunit : Candidate.v ^ 2 + Candidate.u ^ 2 = 1 := by
    nlinarith [Candidate.v_sq_v, Candidate.u_sq_v]
  apply Prod.ext
  · change Candidate.v * (Candidate.v * d - Candidate.u * lam) -
      Candidate.u * (-Candidate.u * d - Candidate.v * lam) = d
    rw [show Candidate.v * (Candidate.v * d - Candidate.u * lam) -
        Candidate.u * (-Candidate.u * d - Candidate.v * lam) =
        (Candidate.v ^ 2 + Candidate.u ^ 2) * d by ring, hunit]
    ring
  · change -Candidate.u * (Candidate.v * d - Candidate.u * lam) -
      Candidate.v * (-Candidate.u * d - Candidate.v * lam) = lam
    rw [show -Candidate.u * (Candidate.v * d - Candidate.u * lam) -
        Candidate.v * (-Candidate.u * d - Candidate.v * lam) =
        (Candidate.v ^ 2 + Candidate.u ^ 2) * lam by ring, hunit]
    ring

/-- Five consecutive edge recurrences close only in the global rotation
direction. The eigenvector slope is the exact half-angle ratio `c/s`. -/
theorem candidate_five_edge_linearized_rotation_mode
    (x0 x1 x2 x3 x4 x5 : ℝ × ℝ)
    (h01 : x1 = candidateRigidityReflection x0)
    (h12 : x2 = candidateRigidityReflection x1)
    (h23 : x3 = candidateRigidityReflection x2)
    (h34 : x4 = candidateRigidityReflection x3)
    (h45 : x5 = candidateRigidityReflection x4)
    (hclose : x5 = x0) :
    ∃ lam : ℝ, x0.1 = -(Candidate.c / Candidate.s) * lam ∧ x0.2 = lam := by
  have h2 : x2 = x0 := by
    rw [h12, h01]
    exact candidateRigidityReflection_involutive x0
  have h3 : x3 = candidateRigidityReflection x0 := by
    rw [h23, h2]
  have h4 : x4 = x0 := by
    rw [h34, h3]
    exact candidateRigidityReflection_involutive x0
  have h5 : x5 = candidateRigidityReflection x0 := by
    rw [h45, h4]
  have hfix : candidateRigidityReflection x0 = x0 := by
    calc
      candidateRigidityReflection x0 = x5 := h5.symm
      _ = x0 := hclose
  rcases x0 with ⟨d, lam⟩
  have hsecond : -Candidate.u * d - Candidate.v * lam = lam :=
    congrArg Prod.snd hfix
  have hdu : d * Candidate.u = -(1 + Candidate.v) * lam := by
    nlinarith [hsecond]
  have hratio : (Candidate.c / Candidate.s) * Candidate.u =
      1 + Candidate.v := by
    have hs : Candidate.s ≠ 0 := ne_of_gt Candidate.s_pos
    calc
      (Candidate.c / Candidate.s) * Candidate.u =
          Candidate.c / Candidate.s * (2 * Candidate.s * Candidate.c) := by
            rw [← Candidate.two_s_c]
      _ = 2 * Candidate.c ^ 2 := by field_simp [hs]
      _ = 1 + Candidate.v := Candidate.two_c_sq
  have hu : Candidate.u ≠ 0 := ne_of_gt Candidate.u_pos
  have hd : d = -(Candidate.c / Candidate.s) * lam := by
    calc
      d = (d * Candidate.u) / Candidate.u := by field_simp [hu]
      _ = (-(1 + Candidate.v) * lam) / Candidate.u := by rw [hdu]
      _ = -(Candidate.c / Candidate.s) * lam := by
        rw [← hratio]
        field_simp [hu]
  exact ⟨lam, hd, rfl⟩

end CP15
