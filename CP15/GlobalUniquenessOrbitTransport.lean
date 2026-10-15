import CP15.GlobalUniquenessOrbitClosed

open Filter Topology

namespace CP15

theorem centeredCongruent15_refl (q : Fin 15 → Plane) :
    CenteredCongruent15 q q := by
  refine ⟨Equiv.refl _, LinearIsometryEquiv.refl ℝ Plane, ?_⟩
  intro i
  rfl

theorem centeredCongruent15_symm {q r : Fin 15 → Plane}
    (h : CenteredCongruent15 q r) : CenteredCongruent15 r q := by
  rcases h with ⟨σ, T, hq⟩
  refine ⟨σ.symm, T.symm, ?_⟩
  intro i
  simp [hq (σ.symm i)]

theorem centeredCongruent15_trans {q r s : Fin 15 → Plane}
    (hqr : CenteredCongruent15 q r) (hrs : CenteredCongruent15 r s) :
    CenteredCongruent15 q s := by
  rcases hqr with ⟨σ, T, hq⟩
  rcases hrs with ⟨τ, U, hr⟩
  refine ⟨σ.trans τ, U.trans T, ?_⟩
  intro i
  simp [hq i, hr (σ i)]

theorem feasible_of_centeredCongruent15
    (q r : Fin 15 → Plane) (b : ℝ)
    (hqr : CenteredCongruent15 q r) (hr : r ∈ FeasibleSet15 b) :
    q ∈ FeasibleSet15 b := by
  rcases hqr with ⟨σ, T, hq⟩
  constructor
  · intro i
    rw [hq i, T.norm_map]
    exact hr.1 (σ i)
  · intro i j hij
    have hne : σ i ≠ σ j := by
      intro he
      exact hij (σ.injective he)
    have hs := hr.2 (σ i) (σ j) hne
    simpa [hq i, hq j] using hs

private noncomputable def normalizedConfiguration (σ : Fin 15 ≃ Fin 15)
    (T : Plane ≃ₗᵢ[ℝ] Plane) (q : Fin 15 → Plane) : Fin 15 → Plane :=
  fun i => T.symm (q (σ.symm i))

private theorem normalizedConfiguration_feasible
    (σ : Fin 15 ≃ Fin 15) (T : Plane ≃ₗᵢ[ℝ] Plane)
    (q : Fin 15 → Plane) (b : ℝ) (hq : q ∈ FeasibleSet15 b) :
    normalizedConfiguration σ T q ∈ FeasibleSet15 b := by
  constructor
  · intro i
    change ‖T.symm (q (σ.symm i))‖ ≤ b
    simpa using hq.1 (σ.symm i)
  · intro i j hij
    change 2 ≤ dist (T.symm (q (σ.symm i))) (T.symm (q (σ.symm j)))
    have hne : σ.symm i ≠ σ.symm j := by
      intro he
      apply hij
      exact σ.injective (by simpa using congrArg σ he)
    have hs := hq.2 (σ.symm i) (σ.symm j) hne
    simpa using hs

private theorem normalizedConfiguration_congruent
    (σ : Fin 15 ≃ Fin 15) (T : Plane ≃ₗᵢ[ℝ] Plane)
    (q : Fin 15 → Plane) :
    CenteredCongruent15 q (normalizedConfiguration σ T q) := by
  refine ⟨σ, T, ?_⟩
  intro i
  simp [normalizedConfiguration]

/-- A neighborhood in the candidate orbit transfers to every point of the
orbit by relabeling and an orthogonal coordinate change. -/
theorem eventually_candidateOrbit_of_local_at_congruent
    (q r : Fin 15 → Plane)
    (hqr : CenteredCongruent15 q r)
    (hlocal : ∀ᶠ z : Fin 15 → Plane in 𝓝 r,
      z ∈ FeasibleSet15 candidateB → z ∈ CandidateCongruenceOrbit15) :
    ∀ᶠ z : Fin 15 → Plane in 𝓝 q,
      z ∈ FeasibleSet15 candidateB → z ∈ CandidateCongruenceOrbit15 := by
  rcases hqr with ⟨σ, T, hpoint⟩
  let N := normalizedConfiguration σ T
  have hNq : N q = r := by
    funext i
    simp [N, normalizedConfiguration, hpoint (σ.symm i)]
  have hcont : Continuous N := by
    apply continuous_pi
    intro i
    exact T.symm.continuous.comp (continuous_apply (σ.symm i))
  have hnear : ∀ᶠ z : Fin 15 → Plane in 𝓝 q,
      N z ∈ FeasibleSet15 candidateB →
        N z ∈ CandidateCongruenceOrbit15 := by
    have ht := hcont.tendsto q
    rw [hNq] at ht
    exact ht.eventually hlocal
  filter_upwards [hnear] with z hz hzfeasible
  have hnfeasible := normalizedConfiguration_feasible σ T z candidateB hzfeasible
  have hnorbit := hz hnfeasible
  exact centeredCongruent15_trans
    (normalizedConfiguration_congruent σ T z) hnorbit

/-- If one feasible point of the candidate orbit has the local alternating
rigidity hypotheses, then every point of the orbit inherits the same local
isolation property. -/
theorem eventually_candidateOrbit_at_every_orbit_point
    (r : Fin 15 → Plane)
    (hrLocal : ∀ᶠ z : Fin 15 → Plane in 𝓝 r,
      z ∈ FeasibleSet15 candidateB → z ∈ CandidateCongruenceOrbit15)
    (hrOrbit : r ∈ CandidateCongruenceOrbit15) :
    ∀ q ∈ CandidateCongruenceOrbit15,
      ∀ᶠ z : Fin 15 → Plane in 𝓝 q,
        z ∈ FeasibleSet15 candidateB → z ∈ CandidateCongruenceOrbit15 := by
  intro q hq
  have hqr : CenteredCongruent15 q r :=
    centeredCongruent15_trans hq (centeredCongruent15_symm hrOrbit)
  exact eventually_candidateOrbit_of_local_at_congruent q r hqr hrLocal

theorem candidate_mem_FeasibleSet15 :
    Candidate.pointAtSeparationTwo ∈ FeasibleSet15 candidateB := by
  constructor
  · intro i
    change ‖scale 2 Candidate.point i‖ ≤ candidateB
    rw [norm_scale 2 (by norm_num)]
    have h := Candidate.all_radius_le i
    rw [← Candidate.two_rho_eq_candidateB]
    nlinarith
  · intro i j hij
    change 2 ≤ dist (scale 2 Candidate.point i)
      (scale 2 Candidate.point j)
    rw [dist_scale 2 (by norm_num)]
    have h := Candidate.separated_point i j hij
    nlinarith

/-- Any strictly ordered angular lift whose span is less than one full turn
can be rotated into the principal argument chart. Choosing the phase halfway
through the complementary gap keeps every rotated ray off the branch cut. -/
theorem exists_rotation_with_strictPolarArg_of_angular_lift
    (q : Fin 15 → Plane) (θ : Fin 15 → ℝ)
    (hmono : StrictMono θ)
    (hspan : θ 14 - θ 0 < 2 * Real.pi)
    (hnonzero : ∀ i, q i ≠ 0)
    (hpolar : ∀ i, planeComplex (q i) =
      ((‖q i‖ : ℝ) : ℂ) *
        (Real.cos (θ i) + Real.sin (θ i) * Complex.I)) :
    ∃ a : Circle,
      StrictMono (fun i => polarArg (planeRotation a (q i))) ∧
      ∀ i, planeComplex (planeRotation a (q i)) ∈ Complex.slitPlane := by
  let δ : ℝ := -(θ 0 + θ 14) / 2
  let a : Circle := Circle.exp δ
  have hθ0 (i : Fin 15) : θ 0 ≤ θ i :=
    hmono.monotone (by omega)
  have hθ14 (i : Fin 15) : θ i ≤ θ 14 :=
    hmono.monotone (by omega)
  have hαlo (i : Fin 15) : -Real.pi < θ i + δ := by
    dsimp [δ]
    linarith [hspan, hθ0 i, hθ14 i]
  have hαhi (i : Fin 15) : θ i + δ < Real.pi := by
    dsimp [δ]
    linarith [hspan, hθ0 i, hθ14 i]
  have hrotate (i : Fin 15) :
      planeComplex (planeRotation a (q i)) =
        ((‖q i‖ : ℝ) : ℂ) *
          (Real.cos (θ i + δ) + Real.sin (θ i + δ) * Complex.I) := by
    calc
      planeComplex (planeRotation a (q i)) =
          (a : ℂ) * planeComplex (q i) := planeComplex_planeRotation a (q i)
      _ = (Real.cos δ + Real.sin δ * Complex.I) *
          (((‖q i‖ : ℝ) : ℂ) *
            (Real.cos (θ i) + Real.sin (θ i) * Complex.I)) := by
            rw [Circle.coe_exp, Complex.exp_mul_I, hpolar i]
            simp only [Complex.ofReal_cos, Complex.ofReal_sin]
      _ = ((‖q i‖ : ℝ) : ℂ) *
          (Real.cos (θ i + δ) + Real.sin (θ i + δ) * Complex.I) := by
            apply Complex.ext <;>
              simp [Complex.mul_re, Complex.mul_im, Real.cos_add,
                Real.sin_add] <;> ring
  have harg (i : Fin 15) :
      polarArg (planeRotation a (q i)) = θ i + δ := by
    rw [polarArg, hrotate]
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
      (Complex.arg_mul_cos_add_sin_mul_I
        (r := ‖q i‖) (norm_pos_iff.mpr (hnonzero i))
        (θ := θ i + δ) ⟨hαlo i, (hαhi i).le⟩)
  refine ⟨a, ?_, ?_⟩
  · intro i j hij
    change polarArg (planeRotation a (q i)) <
      polarArg (planeRotation a (q j))
    rw [harg i, harg j]
    linarith [hmono hij]
  · intro i
    have hz : planeComplex (planeRotation a (q i)) ≠ 0 := by
      intro heq
      have hzero : planeRotation a (q i) = 0 := by
        ext j
        fin_cases j
        · simpa [planeComplex] using congrArg Complex.re heq
        · simpa [planeComplex] using congrArg Complex.im heq
      have hzero' : planeRotation a (q i) = planeRotation a 0 := by
        simpa using hzero
      exact hnonzero i ((planeRotation a).injective hzero')
    have harglt : polarArg (planeRotation a (q i)) < Real.pi := by
      rw [harg i]
      exact hαhi i
    have hsign := (Complex.arg_lt_pi_iff.mp (by simpa [polarArg] using harglt))
    rw [Complex.mem_slitPlane_iff]
    rcases hsign with hre | him
    · by_cases hre0 : (planeComplex (planeRotation a (q i))).re = 0
      · right
        intro him0
        apply hz
        apply Complex.ext
        · exact hre0
        · exact him0
      · left
        exact lt_of_le_of_ne hre (Ne.symm hre0)
    · exact Or.inr him
/-- Under one local isolation certificate, every connected component based at
any point of the candidate orbit stays inside the orbit. The argument uses
the relative topology on the feasible subtype. -/
theorem connectedComponentIn_subset_orbit_of_local_reference
    (r : Fin 15 → Plane)
    (hrOrbit : r ∈ CandidateCongruenceOrbit15)
    (hlocal : ∀ᶠ z : Fin 15 → Plane in 𝓝 r,
      z ∈ FeasibleSet15 candidateB → z ∈ CandidateCongruenceOrbit15) :
    ∀ q, q ∈ CandidateCongruenceOrbit15 →
      ∀ x, x ∈ connectedComponentIn (FeasibleSet15 candidateB) q →
        x ∈ CandidateCongruenceOrbit15 := by
  letI : TopologicalSpace (FeasiblePacking15 candidateB) :=
    TopologicalSpace.induced Subtype.val inferInstance
  let A : Set (FeasiblePacking15 candidateB) :=
    {p | p.1 ∈ CandidateCongruenceOrbit15}
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxOrbit : x.1 ∈ CandidateCongruenceOrbit15 := by
      simpa [A] using hx
    have hlocalx := eventually_candidateOrbit_at_every_orbit_point
      r hlocal hrOrbit x.1 hxOrbit
    have hsubtype := (continuous_subtype_val.tendsto x).eventually hlocalx
    filter_upwards [hsubtype] with y hy
    exact hy y.2
  have hclosed : IsClosed A :=
    isClosed_candidateCongruenceOrbit15.preimage continuous_subtype_val
  have hclopen : IsClopen A := ⟨hclosed, hopen⟩
  intro q hq x hx
  have hqFeasible : q ∈ FeasibleSet15 candidateB := by
    rcases hq with ⟨σ, T, hq⟩
    exact feasible_of_centeredCongruent15 q Candidate.pointAtSeparationTwo
      candidateB ⟨σ, T, hq⟩ candidate_mem_FeasibleSet15
  let c : FeasiblePacking15 candidateB := ⟨q, hqFeasible⟩
  have hcOrbit : c ∈ A := by
    change q ∈ CandidateCongruenceOrbit15
    exact hq
  have hcomponent : connectedComponent c ⊆ A :=
    hclopen.connectedComponent_subset hcOrbit
  rw [connectedComponentIn_eq_image hqFeasible] at hx
  change ∃ p : FeasiblePacking15 candidateB,
      p ∈ connectedComponent c ∧ p.1 = x at hx
  rcases hx with ⟨p, hp, hpx⟩
  subst x
  exact hcomponent hp

/-- Once one point of the candidate orbit has a certified local alternating
neighborhood, the entire candidate connected component is forced into that
orbit. Closedness is unconditional; relative openness is transported from
the one reference point by all relabelings and plane isometries. -/
theorem candidateComponent_subset_orbit_of_local_reference
    (r : Fin 15 → Plane)
    (hrOrbit : r ∈ CandidateCongruenceOrbit15)
    (hlocal : ∀ᶠ z : Fin 15 → Plane in 𝓝 r,
      z ∈ FeasibleSet15 candidateB → z ∈ CandidateCongruenceOrbit15) :
    ∀ q, q ∈ connectedComponentIn (FeasibleSet15 candidateB)
      Candidate.pointAtSeparationTwo → q ∈ CandidateCongruenceOrbit15 := by
  intro q hq
  have hcandidateOrbit :
      Candidate.pointAtSeparationTwo ∈ CandidateCongruenceOrbit15 := by
    change CenteredCongruent15 Candidate.pointAtSeparationTwo
      Candidate.pointAtSeparationTwo
    exact centeredCongruent15_refl _
  exact connectedComponentIn_subset_orbit_of_local_reference r hrOrbit hlocal
    Candidate.pointAtSeparationTwo hcandidateOrbit q hq

end CP15
