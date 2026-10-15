import CP15.ComponentAscent
import CP15.CandidateInnerCycle

namespace CP15

set_option maxHeartbeats 0

theorem complex_polar_rotation (r θ β : ℝ)
    (hcos : Real.cos β = Candidate.v)
    (hsin : Real.sin β = Candidate.u) :
    ((r * Real.cos (θ + β) : ℂ) +
        (r * Real.sin (θ + β)) * Complex.I) =
      ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
        ((r * Real.cos θ : ℂ) + (r * Real.sin θ) * Complex.I) := by
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Real.cos_add, Real.sin_add, hcos, hsin] <;> ring

theorem complex_polar_rotation_pair (r θ β : ℝ)
    (hcos : Real.cos β = Candidate.v)
    (hsin : Real.sin β = Candidate.u) :
    (⟨r * Real.cos (θ + β), r * Real.sin (θ + β)⟩ : ℂ) =
      ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
        (⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Real.cos_add, Real.sin_add, hcos, hsin] <;> ring

/-- Tight inner angular gaps make every actual inner point the same fixed
complex rotation of its predecessor, including the step across the branch
cut of the principal polar argument. -/
theorem actual_inner_complex_cycle
    (q : Fin 15 → Plane) (ix : Fin 5 → Fin 15) (φ : Fin 5 → ℝ)
    (hr : ∀ i, ‖q (ix i)‖ = candidateInnerRadius)
    (hlift : ∀ i, φ i = polarArg (q (ix i)) ∨
      φ i = polarArg (q (ix i)) + 2 * Real.pi)
    (hgap : ∀ i, cyclicAngleGap φ i = 2 * Real.pi / 5) :
    ∀ i : Fin 5,
      planeComplex (q (ix (i + 1))) =
        ((Candidate.v : ℂ) + Candidate.u * Complex.I) *
          planeComplex (q (ix i)) := by
  have hcos := candidate_cos_two_pi_div_five
  have hsin := candidate_sin_two_pi_div_five
  intro i
  fin_cases i <;> norm_num
  · have hg := hgap 0
    simp [cyclicAngleGap] at hg
    have ha : φ 1 = φ 0 + 2 * Real.pi / 5 := by linarith
    have hp0 := planeComplex_eq_polar_coordinates (q (ix 0)) (φ 0) (hlift 0)
    have hp1 := planeComplex_eq_polar_coordinates (q (ix 1)) (φ 1) (hlift 1)
    rw [hp0, hp1, hr 0, hr 1, ha]
    exact complex_polar_rotation_pair _ _ _ hcos hsin
  · have hg := hgap 1
    simp [cyclicAngleGap] at hg
    have ha : φ 2 = φ 1 + 2 * Real.pi / 5 := by linarith
    have hp0 := planeComplex_eq_polar_coordinates (q (ix 1)) (φ 1) (hlift 1)
    have hp1 := planeComplex_eq_polar_coordinates (q (ix 2)) (φ 2) (hlift 2)
    rw [hp0, hp1, hr 1, hr 2, ha]
    exact complex_polar_rotation_pair _ _ _ hcos hsin
  · have hg := hgap 2
    simp [cyclicAngleGap] at hg
    have ha : φ 3 = φ 2 + 2 * Real.pi / 5 := by linarith
    have hp0 := planeComplex_eq_polar_coordinates (q (ix 2)) (φ 2) (hlift 2)
    have hp1 := planeComplex_eq_polar_coordinates (q (ix 3)) (φ 3) (hlift 3)
    rw [hp0, hp1, hr 2, hr 3, ha]
    exact complex_polar_rotation_pair _ _ _ hcos hsin
  · have hg := hgap 3
    simp [cyclicAngleGap] at hg
    have ha : φ 4 = φ 3 + 2 * Real.pi / 5 := by linarith
    have hp0 := planeComplex_eq_polar_coordinates (q (ix 3)) (φ 3) (hlift 3)
    have hp1 := planeComplex_eq_polar_coordinates (q (ix 4)) (φ 4) (hlift 4)
    rw [hp0, hp1, hr 3, hr 4, ha]
    exact complex_polar_rotation_pair _ _ _ hcos hsin
  · have hg := hgap 4
    simp [cyclicAngleGap] at hg
    have ha : φ 0 + 2 * Real.pi = φ 4 + 2 * Real.pi / 5 := by linarith
    have hp0 := planeComplex_eq_polar_coordinates (q (ix 4)) (φ 4) (hlift 4)
    have hp1 := planeComplex_eq_polar_coordinates (q (ix 0)) (φ 0) (hlift 0)
    rw [hp0, hp1, hr 4, hr 0]
    have hcos0 : Real.cos (φ 0) = Real.cos (φ 4 + 2 * Real.pi / 5) := by
      rw [← Real.cos_add_two_pi, ha]
    have hsin0 : Real.sin (φ 0) = Real.sin (φ 4 + 2 * Real.pi / 5) := by
      rw [← Real.sin_add_two_pi, ha]
    rw [hcos0, hsin0]
    exact complex_polar_rotation_pair _ _ _ hcos hsin

theorem planeComplex_smul_two (x : Plane) :
    planeComplex (2 • x) = (2 : ℂ) * planeComplex x := by
  apply Complex.ext <;>
    simp [planeComplex, Complex.mul_re, Complex.mul_im]

theorem planeComplex_real_smul_two (x : Plane) :
    planeComplex ((2 : ℝ) • x) = (2 : ℂ) * planeComplex x := by
  apply Complex.ext <;>
    simp [planeComplex, Complex.mul_re, Complex.mul_im, smul_eq_mul]

/-- The actual terminal inner pentagon and the explicit candidate inner
pentagon differ by one common rotation, with their five labels aligned. -/
theorem exists_rotation_matching_inner_pentagon
    (q : Fin 15 → Plane) (ix : Fin 5 → Fin 15) (φ : Fin 5 → ℝ)
    (hr : ∀ i, ‖q (ix i)‖ = candidateInnerRadius)
    (hlift : ∀ i, φ i = polarArg (q (ix i)) ∨
      φ i = polarArg (q (ix i)) + 2 * Real.pi)
    (hgap : ∀ i, cyclicAngleGap φ i = 2 * Real.pi / 5) :
    ∃ a : Circle, ∀ i : Fin 5,
      _root_.rotation a
        (planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex i))) = planeComplex (q (ix i)) := by
  let w : ℂ := (Candidate.v : ℂ) + Candidate.u * Complex.I
  have hactual := actual_inner_complex_cycle q ix φ hr hlift hgap
  have hcandidate (i : Fin 5) :
      planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex (i + 1))) =
        w * planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex i)) := by
    calc
      planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex (i + 1))) =
          (2 : ℂ) * planeComplex (Candidate.point
            (candidateInnerCycleIndex (i + 1))) := by
        change planeComplex ((2 : ℝ) • Candidate.point
          (candidateInnerCycleIndex (i + 1))) = _
        exact planeComplex_real_smul_two _
      _ = (2 : ℂ) * planeComplex
          (candidateRotate72 (Candidate.point (candidateInnerCycleIndex i))) := by
        rw [candidate_inner_cycle_step]
      _ = (2 : ℂ) * (w * planeComplex
          (Candidate.point (candidateInnerCycleIndex i))) := by
        rw [planeComplex_candidateRotate72]
      _ = w * planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex i)) := by
        change (2 : ℂ) * (w * planeComplex
          (Candidate.point (candidateInnerCycleIndex i))) =
          w * planeComplex ((2 : ℝ) • Candidate.point
            (candidateInnerCycleIndex i))
        rw [planeComplex_real_smul_two]
        ring
  let zq := planeComplex (q (ix 0))
  let zp := planeComplex (Candidate.pointAtSeparationTwo
    (candidateInnerCycleIndex 0))
  have hzq : ‖zq‖ = candidateInnerRadius := by
    dsimp [zq]
    rw [planeComplex_norm, hr]
  have hzp : ‖zp‖ = candidateInnerRadius := by
    dsimp [zp]
    rw [planeComplex_norm, candidate_inner_cycle_radius]
  have hrpos := candidateInnerRadius_pos
  have hzp0 : zp ≠ 0 := by
    intro he
    rw [he] at hzp
    simp at hzp
    exact (ne_of_gt hrpos) hzp.symm
  have hnorm : ‖zq / zp‖ = 1 := by
    rw [norm_div, hzq, hzp, div_self (ne_of_gt hrpos)]
  have hunit : zq / zp ∈ Submonoid.unitSphere ℂ := by
    change zq / zp ∈ Metric.sphere (0 : ℂ) 1
    simpa [Metric.mem_sphere] using hnorm
  let a : Circle := ⟨zq / zp, hunit⟩
  have hbase : (zq / zp) * zp = zq := by
    field_simp [hzp0]
  have hmatch0 :
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 0)) = planeComplex (q (ix 0)) := by
    simpa [zp, zq] using hbase
  have hmatch1 :
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 1)) = planeComplex (q (ix 1)) := by
    calc
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex 1)) =
          w * ((zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 0))) := by
        have hc := hcandidate (0 : Fin 5)
        have hc' : planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 1)) =
            w * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 0)) := by simpa using hc
        rw [hc']
        ring
      _ = w * planeComplex (q (ix 0)) := by rw [hmatch0]
      _ = planeComplex (q (ix 1)) := by
        have hq := hactual (0 : Fin 5)
        simpa [w] using hq.symm
  have hmatch2 :
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 2)) = planeComplex (q (ix 2)) := by
    calc
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex 2)) =
          w * ((zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 1))) := by
        have hc := hcandidate (1 : Fin 5)
        have hc' : planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 2)) =
            w * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 1)) := by simpa using hc
        rw [hc']
        ring
      _ = w * planeComplex (q (ix 1)) := by rw [hmatch1]
      _ = planeComplex (q (ix 2)) := by
        have hq := hactual (1 : Fin 5)
        simpa [w] using hq.symm
  have hmatch3 :
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 3)) = planeComplex (q (ix 3)) := by
    calc
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex 3)) =
          w * ((zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 2))) := by
        have hc := hcandidate (2 : Fin 5)
        have hc' : planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 3)) =
            w * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 2)) := by simpa using hc
        rw [hc']
        ring
      _ = w * planeComplex (q (ix 2)) := by rw [hmatch2]
      _ = planeComplex (q (ix 3)) := by
        have hq := hactual (2 : Fin 5)
        simpa [w] using hq.symm
  have hmatch4 :
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex 4)) = planeComplex (q (ix 4)) := by
    calc
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex 4)) =
          w * ((zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 3))) := by
        have hc := hcandidate (3 : Fin 5)
        have hc' : planeComplex (Candidate.pointAtSeparationTwo
            (candidateInnerCycleIndex 4)) =
            w * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex 3)) := by simpa using hc
        rw [hc']
        ring
      _ = w * planeComplex (q (ix 3)) := by rw [hmatch3]
      _ = planeComplex (q (ix 4)) := by
        have hq := hactual (3 : Fin 5)
        simpa [w] using hq.symm
  have hmatchScalar (i : Fin 5) :
      (zq / zp) * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex i)) = planeComplex (q (ix i)) := by
    fin_cases i
    · simpa using hmatch0
    · simpa using hmatch1
    · simpa using hmatch2
    · simpa using hmatch3
    · simpa using hmatch4
  have hmatch (i : Fin 5) :
      _root_.rotation a
        (planeComplex (Candidate.pointAtSeparationTwo
          (candidateInnerCycleIndex i))) = planeComplex (q (ix i)) := by
    rw [_root_.rotation_apply]
    simpa [a] using hmatchScalar i
  exact ⟨a, hmatch⟩

/-- The inner five centers of an arbitrary terminal representative align,
with their actual indices retained, to the candidate inner pentagon by one
common rotation. This is the coordinate bridge for the terminal equality
classification; it does not identify the ten boundary centers. -/
theorem terminal_component_inner_rotation
    (p : FeasiblePacking15 candidateB)
    (hterminal : ¬∃ q : FeasiblePacking15 candidateB,
      ComponentBoundaryStep candidateB p q) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 ∧
      ∃ ix : Fin 5 → Fin 15, ∃ o : Fin 10 → Fin 15,
        ∃ u : Fin 5 → Fin 10, ∃ φ : Fin 5 → ℝ,
          Function.Injective ix ∧ Function.Injective o ∧
          ∃ a : Circle, ∀ i : Fin 5,
            _root_.rotation a
              (planeComplex (Candidate.pointAtSeparationTwo
                (candidateInnerCycleIndex i))) = planeComplex (q (ix i)) := by
  obtain ⟨q, hq, ix, o, u, φ, hix, ho, _, hr, _, _, _,
    hlift, hgap, _, _, _⟩ :=
    terminal_component_actual_angular_equalities p hterminal
  obtain ⟨a, hmatch⟩ :=
    exists_rotation_matching_inner_pentagon q ix φ hr hlift hgap
  exact ⟨q, hq, ix, o, u, φ, hix, ho, a, hmatch⟩

end CP15
