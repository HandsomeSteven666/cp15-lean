import CP15.CandidateOuterCycle
import CP15.ActualOuterCycle
import CP15.UniqueExtensionLocalGeometry

namespace CP15

open scoped InnerProductSpace

/-- Rotation through the candidate's `pi/5` angle, expressed in its exact
algebraic sine and cosine. -/
noncomputable def candidateRotate36 (x : Plane) : Plane :=
  !₂[Candidate.c * x 0 - Candidate.s * x 1,
    Candidate.s * x 0 + Candidate.c * x 1]

noncomputable def candidateRotation36Circle : Circle :=
  ⟨(⟨Candidate.c, Candidate.s⟩ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [Complex.norm_def, Complex.normSq_apply]
    have hpoly : Candidate.c * Candidate.c + Candidate.s * Candidate.s = 1 := by
      nlinarith [Candidate.pentagon_identity]
    rw [hpoly, Real.sqrt_one]⟩

theorem planeComplex_candidateRotate36 (x : Plane) :
    planeComplex (candidateRotate36 x) =
      (⟨Candidate.c, Candidate.s⟩ : ℂ) * planeComplex x := by
  apply Complex.ext <;>
    simp [candidateRotate36, planeComplex, Complex.mul_re,
      Complex.mul_im] <;> ring

theorem candidateRotate36_eq_planeRotation (x : Plane) :
    planeRotation candidateRotation36Circle x = candidateRotate36 x := by
  apply planeComplex_injective
  rw [planeComplex_planeRotation, planeComplex_candidateRotate36]
  rfl

theorem candidate_t_mul_s : Candidate.t * Candidate.s = 1 / 2 := by
  unfold Candidate.t
  field_simp [ne_of_gt Candidate.s_pos]

/-- Three explicitly chosen candidate centers become the canonical seed
coordinates `(1,a)`, `(1,a+2)`, and `(-1,a+2)` after a common rotation.
These are the inner support, the deleted boundary point, and its second
boundary support. -/
theorem candidate_seed_coordinates :
    candidateRotate36 (Candidate.pointAtSeparationTwo 9) =
        Candidate.pt 1 (Candidate.c / Candidate.s) ∧
    candidateRotate36 (Candidate.pointAtSeparationTwo 12) =
        Candidate.pt 1 (Candidate.c / Candidate.s + 2) ∧
    candidateRotate36 (Candidate.pointAtSeparationTwo 14) =
        Candidate.pt (-1) (Candidate.c / Candidate.s + 2) := by
  have hts := candidate_t_mul_s
  have hpc : Candidate.s ^ 2 + Candidate.c ^ 2 = 1 :=
    Candidate.pentagon_identity
  have hs : Candidate.s ≠ 0 := ne_of_gt Candidate.s_pos
  have htwoct : 2 * Candidate.c * Candidate.t = Candidate.c / Candidate.s := by
    unfold Candidate.t
    field_simp [hs]
  have h11 : candidateRotate36 (Candidate.pointAtSeparationTwo 9) =
      Candidate.pt 1 (Candidate.c / Candidate.s) := by
    ext k
    fin_cases k <;>
      simp [candidateRotate36, Candidate.pointAtSeparationTwo,
        Candidate.point, Candidate.pt] <;>
      nlinarith [hts, hpc, htwoct]
  have h12 : candidateRotate36 (Candidate.pointAtSeparationTwo 12) =
      Candidate.pt 1 (Candidate.c / Candidate.s + 2) := by
    ext k
    fin_cases k <;>
      simp [candidateRotate36, Candidate.pointAtSeparationTwo,
        Candidate.point, Candidate.pt] <;>
      nlinarith [hts, hpc, htwoct]
  have h14 : candidateRotate36 (Candidate.pointAtSeparationTwo 14) =
      Candidate.pt (-1) (Candidate.c / Candidate.s + 2) := by
    ext k
    fin_cases k <;>
      simp [candidateRotate36, Candidate.pointAtSeparationTwo,
        Candidate.point, Candidate.pt] <;>
      nlinarith [hts, hpc, htwoct]
  exact ⟨h11, h12, h14⟩

private theorem candidate_point12_on_boundary :
    ‖Candidate.pointAtSeparationTwo 12‖ = candidateB := by
  have hboundary : ‖Candidate.point 12‖ = Candidate.rho :=
    (Candidate.point_on_boundary_iff 12).2 (by decide)
  calc
    ‖Candidate.pointAtSeparationTwo 12‖ =
        2 * ‖Candidate.point 12‖ := by
          rw [Candidate.pointAtSeparationTwo, norm_smul]
          norm_num
    _ = 2 * Candidate.rho := by rw [hboundary]
    _ = candidateB := Candidate.two_rho_eq_candidateB

private theorem dist_pt_sq_le_of_le_two (x y a b : ℝ)
    (h : dist (Candidate.pt x y) (Candidate.pt a b) ≤ 2) :
    (x - a) ^ 2 + (y - b) ^ 2 ≤ 4 := by
  have hsq := Candidate.dist_pt_sq x y a b
  have hn : 0 ≤ dist (Candidate.pt x y) (Candidate.pt a b) := dist_nonneg
  have hprod := mul_nonneg
    (show 0 ≤ 2 - dist (Candidate.pt x y) (Candidate.pt a b) by linarith)
    (show 0 ≤ 2 + dist (Candidate.pt x y) (Candidate.pt a b) by linarith)
  nlinarith

private theorem dist_pt_sq_ge_of_two_le (x y a b : ℝ)
    (h : 2 ≤ dist (Candidate.pt x y) (Candidate.pt a b)) :
    4 ≤ (x - a) ^ 2 + (y - b) ^ 2 := by
  have hsq := Candidate.dist_pt_sq x y a b
  have hn : 0 ≤ dist (Candidate.pt x y) (Candidate.pt a b) := dist_nonneg
  have hprod := mul_nonneg
    (show 0 ≤ dist (Candidate.pt x y) (Candidate.pt a b) - 2 by linarith)
    (show 0 ≤ dist (Candidate.pt x y) (Candidate.pt a b) + 2 by linarith)
  nlinarith

/-- Candidate center 12 has a unique feasible completion whenever the new
point is within distance two of it. The two explicit contacts and the disk
bound are transported to canonical coordinates by an exact isometry. -/
theorem candidate_point12_unique_if_near
    (x : Plane)
    (hnear : dist x (Candidate.pointAtSeparationTwo 12) ≤ 2)
    (hinner : 2 ≤ dist x (Candidate.pointAtSeparationTwo 9))
    (houter : 2 ≤ dist x (Candidate.pointAtSeparationTwo 14))
    (hdisk : ‖x‖ ≤ candidateB) :
    x = Candidate.pointAtSeparationTwo 12 := by
  let T : Plane ≃ₗᵢ[ℝ] Plane := planeRotation candidateRotation36Circle
  have hrot (z : Plane) : T z = candidateRotate36 z := by
    exact candidateRotate36_eq_planeRotation z
  have htarget : T (Candidate.pointAtSeparationTwo 12) =
      Candidate.pt 1 (Candidate.c / Candidate.s + 2) := by
    rw [hrot, candidate_seed_coordinates.2.1]
  have hsupport1 : T (Candidate.pointAtSeparationTwo 9) =
      Candidate.pt 1 (Candidate.c / Candidate.s) := by
    rw [hrot, candidate_seed_coordinates.1]
  have hsupport2 : T (Candidate.pointAtSeparationTwo 14) =
      Candidate.pt (-1) (Candidate.c / Candidate.s + 2) := by
    rw [hrot, candidate_seed_coordinates.2.2]
  have hnearT : dist (T x) (Candidate.pt 1
      (Candidate.c / Candidate.s + 2)) ≤ 2 := by
    calc
      dist (T x) (Candidate.pt 1 (Candidate.c / Candidate.s + 2)) =
          dist (T x) (T (Candidate.pointAtSeparationTwo 12)) := by rw [htarget]
      _ = dist x (Candidate.pointAtSeparationTwo 12) := T.dist_map x _
      _ ≤ 2 := hnear
  have hinnerT : 2 ≤ dist (T x) (Candidate.pt 1
      (Candidate.c / Candidate.s)) := by
    calc
      2 ≤ dist x (Candidate.pointAtSeparationTwo 9) := hinner
      _ = dist (T x) (T (Candidate.pointAtSeparationTwo 9)) :=
        (T.dist_map x _).symm
      _ = dist (T x) (Candidate.pt 1 (Candidate.c / Candidate.s)) := by
        rw [hsupport1]
  have houterT : 2 ≤ dist (T x) (Candidate.pt (-1)
      (Candidate.c / Candidate.s + 2)) := by
    calc
      2 ≤ dist x (Candidate.pointAtSeparationTwo 14) := houter
      _ = dist (T x) (T (Candidate.pointAtSeparationTwo 14)) :=
        (T.dist_map x _).symm
      _ = dist (T x) (Candidate.pt (-1)
          (Candidate.c / Candidate.s + 2)) := by rw [hsupport2]
  have hdiskT : ‖T x‖ ≤ candidateB := by
    rw [T.norm_map]
    exact hdisk
  let y := T x
  let X := y 0
  let Y := y 1
  change dist y (Candidate.pt 1 (Candidate.c / Candidate.s + 2)) ≤ 2 at hnearT
  change 2 ≤ dist y (Candidate.pt 1 (Candidate.c / Candidate.s)) at hinnerT
  change 2 ≤ dist y (Candidate.pt (-1)
    (Candidate.c / Candidate.s + 2)) at houterT
  change ‖y‖ ≤ candidateB at hdiskT
  have hy : y = Candidate.pt X Y := by
    ext k
    fin_cases k <;> simp [X, Y, Candidate.pt]
  rw [hy] at hnearT hinnerT houterT
  have hnearSq := dist_pt_sq_le_of_le_two X Y 1
    (Candidate.c / Candidate.s + 2) hnearT
  have hinnerSq := dist_pt_sq_ge_of_two_le X Y 1
    (Candidate.c / Candidate.s) hinnerT
  have houterSq := dist_pt_sq_ge_of_two_le X Y (-1)
    (Candidate.c / Candidate.s + 2) houterT
  have hnormSq : ‖y‖ ^ 2 = X ^ 2 + Y ^ 2 := by
    rw [hy]
    exact Candidate.norm_pt_sq X Y
  have htargetNorm : ‖T (Candidate.pointAtSeparationTwo 12)‖ = candidateB := by
    rw [T.norm_map, candidate_point12_on_boundary]
  have hBsq : candidateB ^ 2 =
      1 + (Candidate.c / Candidate.s + 2) ^ 2 := by
    have h := congrArg (fun z : Plane => ‖z‖ ^ 2) htarget
    rw [Candidate.norm_pt_sq] at h
    rw [htargetNorm] at h
    simpa using h
  have hnormle : ‖y‖ ^ 2 ≤ candidateB ^ 2 := by
    have hprod := mul_nonneg
      (show 0 ≤ candidateB - ‖y‖ by linarith [hdiskT])
      (show 0 ≤ candidateB + ‖y‖ by positivity [candidateB_pos])
    nlinarith
  have hdiskSq : X ^ 2 + Y ^ 2 ≤
      1 + (Candidate.c / Candidate.s + 2) ^ 2 := by
    rw [hnormSq, hBsq] at hnormle
    exact hnormle
  let a := Candidate.c / Candidate.s
  let dx := X - 1
  let dy := Y - (a + 2)
  have hlocal := seed_boundary_point_unique_within_radius_two
    a dx dy Candidate.ratio_local_bounds.1
    (by nlinarith [Candidate.ratio_local_bounds.2])
    (by dsimp [dx, dy]; nlinarith [hnearSq])
    (by dsimp [dx, dy, a]; nlinarith [hinnerSq])
    (by dsimp [dx, dy, a]; nlinarith [houterSq])
    (by dsimp [dx, dy, a]; nlinarith [hdiskSq])
  rcases hlocal with ⟨hdx, hdy⟩
  have hyTarget : y = Candidate.pt 1 (a + 2) := by
    rw [hy]
    have hX : X = 1 := by dsimp [dx] at hdx; linarith
    have hY : Y = a + 2 := by dsimp [dy] at hdy; linarith
    rw [hX, hY]
  have hTx : T x = T (Candidate.pointAtSeparationTwo 12) := by
    rw [hrot x, hrot (Candidate.pointAtSeparationTwo 12),
      candidate_seed_coordinates.2.1]
    exact hyTarget
  exact T.injective hTx

end CP15
