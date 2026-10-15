import CP15.GlobalUniquenessLocalIsolation
import Mathlib.Analysis.Complex.Isometry

open scoped InnerProductSpace
open scoped ComplexConjugate

namespace CP15

private def complexToPlane (z : ℂ) : Plane := !₂[z.re, z.im]

private theorem planeComplex_complexToPlane (z : ℂ) :
    planeComplex (complexToPlane z) = z := by
  apply Complex.ext <;> simp [planeComplex, complexToPlane]

private theorem complexToPlane_planeComplex (x : Plane) :
    complexToPlane (planeComplex x) = x := by
  ext i
  fin_cases i <;> simp [planeComplex, complexToPlane]

private def planeComplexLinear : Plane →ₗ[ℝ] ℂ where
  toFun := planeComplex
  map_add' x y := by
    apply Complex.ext <;> simp [planeComplex]
  map_smul' a x := by
    apply Complex.ext <;> simp [planeComplex]

private def complexToPlaneLinear : ℂ →ₗ[ℝ] Plane where
  toFun := complexToPlane
  map_add' x y := by
    ext i
    fin_cases i <;> simp [complexToPlane]
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [complexToPlane]

private theorem continuous_complexToPlane : Continuous complexToPlane := by
  have hnorm (z : ℂ) : ‖complexToPlane z‖ = ‖z‖ := by
    rw [← planeComplex_norm, planeComplex_complexToPlane]
  have hiso : Isometry complexToPlane := by
    intro x y
    rw [edist_dist, edist_dist]
    congr 1
    calc
      dist (complexToPlane x) (complexToPlane y) =
          ‖complexToPlane x - complexToPlane y‖ := dist_eq_norm _ _
      _ = ‖complexToPlane (x - y)‖ := by
        congr 1
        ext i
        fin_cases i <;> simp [complexToPlane]
      _ = ‖x - y‖ := hnorm _
      _ = dist x y := (dist_eq_norm _ _).symm
  exact hiso.continuous

private def planeComplexLinearIsometry : Plane →ₗᵢ[ℝ] ℂ :=
  { planeComplexLinear with norm_map' := planeComplex_norm }

private noncomputable def planeComplexLinearIsometryEquiv : Plane ≃ₗᵢ[ℝ] ℂ := by
  have hfg : planeComplexLinear.comp complexToPlaneLinear = LinearMap.id := by
    apply LinearMap.ext
    intro z
    exact planeComplex_complexToPlane z
  have hgf : complexToPlaneLinear.comp planeComplexLinear = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact complexToPlane_planeComplex x
  exact LinearIsometryEquiv.ofLinearIsometry planeComplexLinearIsometry
    complexToPlaneLinear hfg hgf

private theorem planeComplexLinearIsometryEquiv_apply (x : Plane) :
    planeComplexLinearIsometryEquiv x = planeComplex x := rfl

private def planeConjugationLinear : Plane →ₗ[ℝ] Plane where
  toFun x := !₂[x 0, -x 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp

private theorem planeComplex_conjugation (x : Plane) :
    planeComplex (planeConjugationLinear x) = star (planeComplex x) := by
  apply Complex.ext <;> simp [planeComplex, planeConjugationLinear]

private noncomputable def planeConjugation : Plane ≃ₗᵢ[ℝ] Plane := by
  let f : Plane →ₗᵢ[ℝ] Plane :=
    { planeConjugationLinear with
      norm_map' := by
        intro x
        rw [← planeComplex_norm, planeComplex_conjugation, norm_star,
          planeComplex_norm] }
  have hff : planeConjugationLinear.comp planeConjugationLinear = LinearMap.id := by
    apply LinearMap.ext
    intro x
    ext i
    fin_cases i <;> simp [planeConjugationLinear]
  exact LinearIsometryEquiv.ofLinearIsometry f planeConjugationLinear hff hff

private theorem planeComplex_planeConjugation (x : Plane) :
    planeComplex (planeConjugation x) = star (planeComplex x) := by
  change planeComplex (planeConjugationLinear x) = _
  exact planeComplex_conjugation x

private theorem plane_isometry_classification
    (T : Plane ≃ₗᵢ[ℝ] Plane) :
    ∃ a : Circle,
      T = planeRotation a ∨
        T = planeConjugation.trans (planeRotation a) := by
  let E := planeComplexLinearIsometryEquiv
  let F : ℂ ≃ₗᵢ[ℝ] ℂ := E.symm.trans (T.trans E)
  obtain ⟨a, hrot | hconj⟩ := linear_isometry_complex F
  · refine ⟨a, Or.inl ?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    apply planeComplex_injective
    have hF (x : Plane) : F (planeComplex x) = planeComplex (T x) := by
      change E (T (E.symm (planeComplex x))) = planeComplex (T x)
      rw [show E.symm (planeComplex x) = x by
        rw [← planeComplexLinearIsometryEquiv_apply]
        exact E.symm_apply_apply x]
      rfl
    calc
      planeComplex (T x) = F (planeComplex x) := (hF x).symm
      _ = rotation a (planeComplex x) := by rw [hrot]
      _ = planeComplex (planeRotation a x) := by
        rw [rotation_apply, planeComplex_planeRotation]
  · refine ⟨a, Or.inr ?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    apply planeComplex_injective
    have hF (x : Plane) : F (planeComplex x) = planeComplex (T x) := by
      change E (T (E.symm (planeComplex x))) = planeComplex (T x)
      rw [show E.symm (planeComplex x) = x by
        rw [← planeComplexLinearIsometryEquiv_apply]
        exact E.symm_apply_apply x]
      rfl
    calc
      planeComplex (T x) = F (planeComplex x) := (hF x).symm
      _ = (Complex.conjLIE.trans (rotation a)) (planeComplex x) := by rw [hconj]
      _ = planeComplex ((planeConjugation.trans (planeRotation a)) x) := by
        change rotation a (Complex.conjLIE (planeComplex x)) =
          planeComplex (planeRotation a (planeConjugation x))
        rw [show Complex.conjLIE (planeComplex x) = star (planeComplex x) by rfl,
          planeComplex_planeRotation, planeComplex_planeConjugation, rotation_apply]

/-- The congruence orbit of the candidate is a finite union of compact
rotation and reflection images, hence is closed in the configuration space. -/
def CandidateCongruenceOrbit15 : Set (Fin 15 → Plane) :=
  {q | CenteredCongruent15 q Candidate.pointAtSeparationTwo}

private noncomputable def candidateOrbitParam (σ : Fin 15 ≃ Fin 15) (flip : Bool) :
    Circle → Fin 15 → Plane := fun a i =>
  planeRotation a
    (if flip then planeConjugation (Candidate.pointAtSeparationTwo (σ i))
      else Candidate.pointAtSeparationTwo (σ i))

private theorem continuous_planeRotation_at (x : Plane) :
    Continuous (fun a : Circle => planeRotation a x) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hcoords :
      (fun a : Circle => planeRotation a x) =
        fun a : Circle => complexToPlane ((a : ℂ) * planeComplex x) := by
    funext a
    apply planeComplex_injective
    simp only [planeComplex_complexToPlane, planeComplex_planeRotation]
  rw [hcoords]
  have hm : Continuous (fun a : Circle => (a : ℂ) * planeComplex x) := by
    fun_prop
  exact (continuous_complexToPlane.comp hm).continuousAt

private theorem continuous_candidateOrbitParam
    (σ : Fin 15 ≃ Fin 15) (flip : Bool) :
    Continuous (candidateOrbitParam σ flip) := by
  apply continuous_pi
  intro i
  by_cases h : flip
  · simp [candidateOrbitParam, h]
    exact continuous_planeRotation_at _
  · simp [candidateOrbitParam, h]
    exact continuous_planeRotation_at _

private theorem candidateCongruenceOrbit_eq_parametric_union :
    CandidateCongruenceOrbit15 =
      ⋃ σ : Fin 15 ≃ Fin 15, ⋃ flip : Bool,
        Set.range (candidateOrbitParam σ flip) := by
  classical
  ext q
  constructor
  · rintro ⟨σ, T, hq⟩
    obtain ⟨a, hT | hT⟩ := plane_isometry_classification T
    · refine Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨false, ?_⟩⟩
      refine ⟨a, ?_⟩
      funext i
      simp [candidateOrbitParam, hT, hq]
    · refine Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨true, ?_⟩⟩
      refine ⟨a, ?_⟩
      funext i
      simp [candidateOrbitParam, hT, hq]
  · intro hq
    rcases Set.mem_iUnion.mp hq with ⟨σ, hq⟩
    rcases Set.mem_iUnion.mp hq with ⟨flip, hq⟩
    rcases Set.mem_range.mp hq with ⟨a, rfl⟩
    refine ⟨σ, (if flip then planeConjugation.trans (planeRotation a)
      else planeRotation a), ?_⟩
    intro i
    by_cases h : flip <;> simp [candidateOrbitParam, h]

private theorem isCompact_candidateOrbitParam_range
    (σ : Fin 15 ≃ Fin 15) (flip : Bool) :
    IsCompact (Set.range (candidateOrbitParam σ flip)) := by
  have h := isCompact_univ.image (continuous_candidateOrbitParam σ flip)
  convert h using 1
  ext q
  simp

private theorem isCompact_candidateCongruenceOrbit15 :
    IsCompact CandidateCongruenceOrbit15 := by
  classical
  rw [candidateCongruenceOrbit_eq_parametric_union]
  simpa only [Set.biUnion_univ] using
    (Set.finite_univ : (Set.univ : Set (Fin 15 ≃ Fin 15)).Finite).isCompact_biUnion
      (fun σ _ =>
        (Set.finite_univ : (Set.univ : Set Bool).Finite).isCompact_biUnion
          (fun flip _ => isCompact_candidateOrbitParam_range σ flip))

theorem isClosed_candidateCongruenceOrbit15 :
    IsClosed CandidateCongruenceOrbit15 := by
  exact isCompact_candidateCongruenceOrbit15.isClosed

end CP15
