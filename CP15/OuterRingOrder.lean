import CP15.OuterExistence
import CP15.BasicAngleBounds

namespace CP15

/-- Coordinate identification used only to sort boundary centers by polar
argument. -/
def planeComplex (x : Plane) : ℂ := ⟨x 0, x 1⟩

theorem planeComplex_norm (x : Plane) : ‖planeComplex x‖ = ‖x‖ := by
  have hc : ‖planeComplex x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [Complex.sq_norm]
    simp [planeComplex, Complex.normSq_apply]
    ring
  have hp : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  nlinarith [norm_nonneg (planeComplex x), norm_nonneg x]

theorem planeComplex_injective : Function.Injective planeComplex := by
  intro x y h
  ext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

noncomputable def polarArg (x : Plane) : ℝ :=
  Complex.arg (planeComplex x)

theorem polarArg_range (x : Plane) :
    -Real.pi < polarArg x ∧ polarArg x ≤ Real.pi :=
  Complex.arg_mem_Ioc (planeComplex x)

/-- On a common circle, equal polar arguments force equal centers. This is
the injectivity needed to sort the boundary centers without tie ambiguity. -/
theorem boundary_polarArg_injective (p : Fin 15 → Plane) (b : ℝ)
    (hsep : Separated p 2)
    (i j : Fin 15) (hi : ‖p i‖ = b) (hj : ‖p j‖ = b)
    (harg : polarArg (p i) = polarArg (p j)) : i = j := by
  have hnorm : ‖planeComplex (p i)‖ = ‖planeComplex (p j)‖ := by
    rw [planeComplex_norm, planeComplex_norm, hi, hj]
  have heq : planeComplex (p i) = planeComplex (p j) :=
    Complex.ext_norm_arg hnorm harg
  have hp : p i = p j := planeComplex_injective heq
  by_contra hij
  have hd := hsep i j hij
  rw [hp] at hd
  norm_num at hd

end CP15
