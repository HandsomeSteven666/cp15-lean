import CP15.CandidateOuterCycle
import CP15.UniqueExtensionSymmetry

namespace CP15

set_option maxHeartbeats 0

open scoped InnerProductSpace

def candidateAllIndex : Fin 5 ⊕ (Fin 5 ⊕ Fin 5) → Fin 15
  | Sum.inl i => candidateInnerCycleIndex i
  | Sum.inr (Sum.inl i) => candidateOuterStartIndex i
  | Sum.inr (Sum.inr i) => candidateOuterEndIndex i

theorem candidateAllIndex_bijective : Function.Bijective candidateAllIndex := by
  decide

noncomputable def candidateAllEquiv :
    Fin 5 ⊕ (Fin 5 ⊕ Fin 5) ≃ Fin 15 :=
  Equiv.ofBijective candidateAllIndex candidateAllIndex_bijective

def actualAllIndex (ix : Fin 5 → Fin 15) (o : Fin 10 → Fin 15)
    (u : Fin 5 → Fin 10) : Fin 5 ⊕ (Fin 5 ⊕ Fin 5) → Fin 15
  | Sum.inl i => ix i
  | Sum.inr (Sum.inl i) => o (u i)
  | Sum.inr (Sum.inr i) => o (u i + 1)

def planeRotateLinear (a : Circle) : Plane →ₗ[ℝ] Plane where
  toFun x := !₂[(a : ℂ).re * x 0 - (a : ℂ).im * x 1,
    (a : ℂ).im * x 0 + (a : ℂ).re * x 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

theorem planeComplex_planeRotateLinear (a : Circle) (x : Plane) :
    planeComplex (planeRotateLinear a x) = (a : ℂ) * planeComplex x := by
  apply Complex.ext <;>
    simp [planeComplex, planeRotateLinear, Complex.mul_re, Complex.mul_im] <;> ring

noncomputable def planeRotation (a : Circle) : Plane ≃ₗᵢ[ℝ] Plane := by
  let f : Plane →ₗᵢ[ℝ] Plane :=
    { planeRotateLinear a with
      norm_map' := by
        intro x
        rw [← planeComplex_norm, planeComplex_planeRotateLinear, norm_mul,
          Circle.norm_coe, one_mul, planeComplex_norm] }
  let g := planeRotateLinear a⁻¹
  have hfgPoint (x : Plane) : f (g x) = x := by
    apply planeComplex_injective
    simp [f, g, planeComplex_planeRotateLinear, mul_assoc]
  have hgfPoint (x : Plane) : g (f x) = x := by
    apply planeComplex_injective
    simp [f, g, planeComplex_planeRotateLinear, mul_assoc]
  have hfg : f.toLinearMap.comp g = LinearMap.id := by
    exact LinearMap.ext hfgPoint
  have hgf : g.comp f.toLinearMap = LinearMap.id := by
    exact LinearMap.ext hgfPoint
  exact LinearIsometryEquiv.ofLinearIsometry f g hfg hgf

theorem planeComplex_planeRotation (a : Circle) (x : Plane) :
    planeComplex (planeRotation a x) = (a : ℂ) * planeComplex x := by
  change planeComplex (planeRotateLinear a x) = _
  exact planeComplex_planeRotateLinear a x

def actualOuterPairIndex (u : Fin 5 → Fin 10) :
    Fin 5 ⊕ Fin 5 → Fin 10
  | Sum.inl i => u i
  | Sum.inr i => u i + 1

def evenOuterStart (i : Fin 5) : Fin 10 :=
  ⟨2 * i.val, by omega⟩

def oddOuterStart (i : Fin 5) : Fin 10 :=
  ⟨2 * i.val + 1, by omega⟩

def evenOuterPairIndex : Fin 5 ⊕ Fin 5 → Fin 10
  | Sum.inl i => evenOuterStart i
  | Sum.inr i => evenOuterStart i + 1

def oddOuterPairIndex : Fin 5 ⊕ Fin 5 → Fin 10
  | Sum.inl i => oddOuterStart i
  | Sum.inr i => oddOuterStart i + 1

theorem evenOuterPairIndex_bijective :
    Function.Bijective evenOuterPairIndex := by decide

theorem oddOuterPairIndex_bijective :
    Function.Bijective oddOuterPairIndex := by decide

theorem actualOuterPairIndex_bijective
    (u : Fin 5 → Fin 10)
    (halternating : ∃ a : Fin 2, ∀ i,
      (u i).val = a.val + 2 * i.val) :
    Function.Bijective (actualOuterPairIndex u) := by
  obtain ⟨a, ha⟩ := halternating
  fin_cases a
  · have hstart (i : Fin 5) : u i = evenOuterStart i := by
      apply Fin.ext
      simpa [evenOuterStart] using ha i
    have hmap : actualOuterPairIndex u = evenOuterPairIndex := by
      funext x
      cases x with
      | inl i => simpa [actualOuterPairIndex, evenOuterPairIndex] using hstart i
      | inr i => simp [actualOuterPairIndex, evenOuterPairIndex, hstart]
    rw [hmap]
    exact evenOuterPairIndex_bijective
  · have hstart (i : Fin 5) : u i = oddOuterStart i := by
      apply Fin.ext
      have hh := ha i
      simp only [Fin.val_zero, Fin.val_one] at hh
      simpa [oddOuterStart, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hh
    have hmap : actualOuterPairIndex u = oddOuterPairIndex := by
      funext x
      cases x with
      | inl i => simpa [actualOuterPairIndex, oddOuterPairIndex] using hstart i
      | inr i => simp [actualOuterPairIndex, oddOuterPairIndex, hstart]
    rw [hmap]
    exact oddOuterPairIndex_bijective

theorem actualAllIndex_bijective
    (q : Fin 15 → Plane) (ix : Fin 5 → Fin 15)
    (o : Fin 10 → Fin 15) (u : Fin 5 → Fin 10)
    (ha : ∃ a : Fin 2, ∀ i, (u i).val = a.val + 2 * i.val)
    (hix : Function.Injective ix) (ho : Function.Injective o)
    (hr : ∀ i, ‖q (ix i)‖ = candidateInnerRadius)
    (hR : ∀ k, ‖q (o k)‖ = candidateB)
    (houter : ∀ j, ‖q j‖ = candidateB → ∃ k, o k = j)
    (hinner : ∀ j, ‖q j‖ < candidateB → ∃ i, ix i = j)
    (hq : q ∈ FeasibleSet15 candidateB) :
    Function.Bijective (actualAllIndex ix o u) := by
  have hri : candidateInnerRadius < candidateB := by
    linarith [candidateInnerRadius_local_bounds.2, candidateB_local_bounds.1]
  have hpairBij := actualOuterPairIndex_bijective u ha
  constructor
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        change ix i = ix j at hxy
        have hij : ix i = ix j := hxy
        exact congrArg Sum.inl (hix hij)
      | inr y' =>
        cases y' with
        | inl j =>
          change ix i = o (u j) at hxy
          have hidx : ix i = o (u j) := hxy
          have hn := congrArg (fun k => ‖q k‖) hidx
          rw [hr i, hR (u j)] at hn
          exact (ne_of_lt hri hn).elim
        | inr j =>
          change ix i = o (u j + 1) at hxy
          have hidx : ix i = o (u j + 1) := hxy
          have hn := congrArg (fun k => ‖q k‖) hidx
          rw [hr i, hR (u j + 1)] at hn
          exact (ne_of_lt hri hn).elim
    | inr x' =>
      cases x' with
      | inl i =>
        cases y with
        | inl j =>
          change o (u i) = ix j at hxy
          have hidx : o (u i) = ix j := hxy
          have hn := congrArg (fun k => ‖q k‖) hidx
          rw [hR (u i), hr j] at hn
          exact (ne_of_lt hri hn.symm).elim
        | inr y' =>
          cases y' with
          | inl j =>
            change o (u i) = o (u j) at hxy
            have hpEq : actualOuterPairIndex u (Sum.inl i) =
                actualOuterPairIndex u (Sum.inl j) := by
              simp [actualOuterPairIndex, ho hxy]
            have hij := hpairBij.1 hpEq
            cases hij
            rfl
          | inr j =>
            change o (u i) = o (u j + 1) at hxy
            have hpair' : actualOuterPairIndex u (Sum.inl i) =
                actualOuterPairIndex u (Sum.inr j) := by
              simp [actualOuterPairIndex, ho hxy]
            have hbad := hpairBij.1 hpair'
            cases hbad
      | inr i =>
        cases y with
        | inl j =>
          change o (u i + 1) = ix j at hxy
          have hidx : o (u i + 1) = ix j := hxy
          have hn := congrArg (fun k => ‖q k‖) hidx
          rw [hR (u i + 1), hr j] at hn
          exact (ne_of_lt hri hn.symm).elim
        | inr y' =>
          cases y' with
          | inl j =>
            change o (u i + 1) = o (u j) at hxy
            have hpair' : actualOuterPairIndex u (Sum.inr i) =
                actualOuterPairIndex u (Sum.inl j) := by
              simp [actualOuterPairIndex, ho hxy]
            have hbad := hpairBij.1 hpair'
            cases hbad
          | inr j =>
            change o (u i + 1) = o (u j + 1) at hxy
            have hpair'' : actualOuterPairIndex u (Sum.inr i) =
                actualOuterPairIndex u (Sum.inr j) := by
              simp [actualOuterPairIndex, ho hxy]
            have hij := hpairBij.1 hpair''
            cases hij
            rfl
  · intro j
    have hjdisk : ‖q j‖ ≤ candidateB := hq.1 j
    by_cases heq : ‖q j‖ = candidateB
    · obtain ⟨k, hk⟩ := houter j heq
      obtain ⟨z, hz⟩ := hpairBij.2 k
      cases z with
      | inl i =>
        have hz' : u i = k := by simpa [actualOuterPairIndex] using hz
        refine ⟨Sum.inr (Sum.inl i), ?_⟩
        simp [actualAllIndex, hz', hk]
      | inr i =>
        have hz' : u i + 1 = k := by simpa [actualOuterPairIndex] using hz
        refine ⟨Sum.inr (Sum.inr i), ?_⟩
        simp [actualAllIndex, hz', hk]
    · have hlt : ‖q j‖ < candidateB := lt_of_le_of_ne hjdisk heq
      obtain ⟨i, hi⟩ := hinner j hlt
      exact ⟨Sum.inl i, by simp [actualAllIndex, hi]⟩


theorem complex_polar_contact_minus (R r θ γ : ℝ) (hr : r ≠ 0) :
    (⟨R * Real.cos (θ - γ), R * Real.sin (θ - γ)⟩ : ℂ) =
      ((R / r : ℝ) : ℂ) *
        (⟨Real.cos γ, -Real.sin γ⟩ : ℂ) *
        (⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ) := by
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Real.cos_sub]
    field_simp [hr]
  · simp [Complex.mul_re, Complex.mul_im, Real.sin_sub]
    field_simp [hr]
    ring

theorem complex_polar_contact_plus (R r θ γ : ℝ) (hr : r ≠ 0) :
    (⟨R * Real.cos (θ + γ), R * Real.sin (θ + γ)⟩ : ℂ) =
      ((R / r : ℝ) : ℂ) *
        (⟨Real.cos γ, Real.sin γ⟩ : ℂ) *
        (⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ) := by
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Real.cos_add]
    field_simp [hr]
  · simp [Complex.mul_re, Complex.mul_im, Real.sin_add]
    field_simp [hr]

theorem planeComplex_contact_start
    (inner outer : Plane) (θ ψ γ : ℝ)
    (hr : ‖inner‖ = candidateInnerRadius)
    (hR : ‖outer‖ = candidateB)
    (harg : polarArg outer = ψ)
    (hinner : θ = polarArg inner ∨
      θ = polarArg inner + 2 * Real.pi)
    (hphase : θ = ψ + γ) :
    planeComplex outer =
      ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
        (⟨Real.cos γ, -Real.sin γ⟩ : ℂ) * planeComplex inner := by
  have houter := planeComplex_eq_polar_coordinates outer ψ
    (Or.inl harg.symm)
  have hinnerPolar := planeComplex_eq_polar_coordinates inner θ hinner
  have hangle : ψ = θ - γ := by linarith
  rw [houter, hinnerPolar, hR, hr, hangle]
  exact complex_polar_contact_minus candidateB candidateInnerRadius θ γ
    (ne_of_gt candidateInnerRadius_pos)

theorem planeComplex_contact_end
    (inner outer : Plane) (θ ψ γ : ℝ)
    (hr : ‖inner‖ = candidateInnerRadius)
    (hR : ‖outer‖ = candidateB)
    (harg : ψ = polarArg outer ∨
      ψ = polarArg outer + 2 * Real.pi)
    (hinner : θ = polarArg inner ∨
      θ = polarArg inner + 2 * Real.pi)
    (hphase : ψ = θ + γ) :
    planeComplex outer =
      ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
        (⟨Real.cos γ, Real.sin γ⟩ : ℂ) * planeComplex inner := by
  have houter := planeComplex_eq_polar_coordinates outer ψ harg
  have hinnerPolar := planeComplex_eq_polar_coordinates inner θ hinner
  rw [houter, hinnerPolar, hR, hr, hphase]
  exact complex_polar_contact_plus candidateB candidateInnerRadius θ γ
    (ne_of_gt candidateInnerRadius_pos)

theorem actual_contact_next_angle
    (ψ : Fin 10 → ℝ) (u : Fin 5 → Fin 10) (φ : Fin 5 → ℝ)
    (γ : ℝ)
    (hphase : ∀ i, φ i = ψ (u i) + γ)
    (hgap : ∀ i, cyclicAngleGap ψ (u i) = 2 * γ)
    (i : Fin 5) :
    ψ (u i + 1) = φ i + γ ∨
      ψ (u i + 1) + 2 * Real.pi = φ i + γ := by
  by_cases hlast : u i = Fin.last 9
  · have hg := hgap i
    have hiLast : u i = (9 : Fin 10) := by simpa [Fin.last] using hlast
    simp [cyclicAngleGap, Fin.last, hiLast] at hg
    have hp : φ i = ψ 9 + γ := by
      simpa [hiLast] using hphase i
    have hnext : u i + 1 = 0 := by simp [hlast]
    rw [hnext]
    right
    linarith
  · have hg := hgap i
    have hiNotLast : u i ≠ (9 : Fin 10) := by
      intro he
      apply hlast
      simpa [Fin.last] using he
    simp [cyclicAngleGap, Fin.last, hiNotLast] at hg
    left
    linarith [hphase i]

/-- Once the actual inner pentagon has been rotated onto the candidate,
the five measured short gaps identify both outer endpoints of every inner
contact pair. The final pair uses the branch-cut alternative explicitly. -/
theorem actual_contact_pairs_match_candidate
    (q : Fin 15 → Plane) (ix : Fin 5 → Fin 15)
    (o : Fin 10 → Fin 15) (u : Fin 5 → Fin 10)
    (φ : Fin 5 → ℝ) (ψ : Fin 10 → ℝ) (a : Circle)
    (hr : ∀ i, ‖q (ix i)‖ = candidateInnerRadius)
    (hR : ∀ k, ‖q (o k)‖ = candidateB)
    (harg : ∀ k, polarArg (q (o k)) = ψ k)
    (hlift : ∀ i, φ i = polarArg (q (ix i)) ∨
      φ i = polarArg (q (ix i)) + 2 * Real.pi)
    (hphase : ∀ i, φ i = ψ (u i) +
      contactAngle candidateB candidateInnerRadius)
    (hgap : ∀ i, cyclicAngleGap ψ (u i) =
      2 * contactAngle candidateB candidateInnerRadius)
    (hrotation : ∀ i, _root_.rotation a
      (planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex i))) = planeComplex (q (ix i))) :
    ∀ i, _root_.rotation a
        (planeComplex (Candidate.pointAtSeparationTwo
          (candidateOuterStartIndex i))) = planeComplex (q (o (u i))) ∧
      _root_.rotation a
        (planeComplex (Candidate.pointAtSeparationTwo
          (candidateOuterEndIndex i))) = planeComplex (q (o (u i + 1))) := by
  intro i
  let γ := contactAngle candidateB candidateInnerRadius
  have hinnerRotation :
      ((a : ℂ) * planeComplex (Candidate.pointAtSeparationTwo
        (candidateInnerCycleIndex i))) = planeComplex (q (ix i)) := by
    simpa [_root_.rotation_apply] using hrotation i
  have hminusFactor :
      ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
        (⟨Real.cos γ, -Real.sin γ⟩ : ℂ) =
      candidateContactFactorMinus := by
    have hunit : (⟨Real.cos γ, -Real.sin γ⟩ : ℂ) =
        Complex.cos (γ : ℂ) - Complex.sin (γ : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.cos_ofReal_re,
          Complex.sin_ofReal_re, Complex.cos_ofReal_im,
          Complex.sin_ofReal_im]
    calc
      ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
          (⟨Real.cos γ, -Real.sin γ⟩ : ℂ) =
          ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
            (Complex.cos (γ : ℂ) - Complex.sin (γ : ℂ) * Complex.I) := by
        rw [hunit]
      _ = candidateContactFactorMinus := by
        simpa [γ, candidateContactFactorMinus] using
          candidate_contact_factor_minus
  have hplusFactor :
      ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
        (⟨Real.cos γ, Real.sin γ⟩ : ℂ) =
      candidateContactFactorPlus := by
    have hunit : (⟨Real.cos γ, Real.sin γ⟩ : ℂ) =
        Complex.cos (γ : ℂ) + Complex.sin (γ : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.cos_ofReal_re,
          Complex.sin_ofReal_re, Complex.cos_ofReal_im,
          Complex.sin_ofReal_im]
    calc
      ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
          (⟨Real.cos γ, Real.sin γ⟩ : ℂ) =
          ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
            (Complex.cos (γ : ℂ) + Complex.sin (γ : ℂ) * Complex.I) := by
        rw [hunit]
      _ = candidateContactFactorPlus := by
        simpa [γ, candidateContactFactorPlus] using
          candidate_contact_factor_plus
  have hstartCoord :
      planeComplex (q (o (u i))) =
        candidateContactFactorMinus * planeComplex (q (ix i)) := by
    have hc := planeComplex_contact_start (q (ix i)) (q (o (u i)))
      (φ i) (ψ (u i)) γ (hr i) (hR (u i)) (harg (u i))
      (hlift i) (hphase i)
    calc
      planeComplex (q (o (u i))) =
          ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
            (⟨Real.cos γ, -Real.sin γ⟩ : ℂ) *
            planeComplex (q (ix i)) := hc
      _ = candidateContactFactorMinus *
            planeComplex (q (ix i)) := by rw [hminusFactor]
  have hnextAngle := actual_contact_next_angle ψ u φ γ hphase hgap i
  have hnextArg :
      φ i + γ = polarArg (q (o (u i + 1))) ∨
        φ i + γ = polarArg (q (o (u i + 1))) + 2 * Real.pi := by
    have ha := harg (u i + 1)
    rcases hnextAngle with h | h
    · exact Or.inl (h.symm.trans ha.symm)
    · exact Or.inr (h.symm.trans (by rw [← ha]))
  have hendCoord :
      planeComplex (q (o (u i + 1))) =
        candidateContactFactorPlus * planeComplex (q (ix i)) := by
    have hc := planeComplex_contact_end (q (ix i))
      (q (o (u i + 1))) (φ i) (φ i + γ) γ
      (hr i) (hR (u i + 1)) hnextArg (hlift i) rfl
    calc
      planeComplex (q (o (u i + 1))) =
          ((candidateB / candidateInnerRadius : ℝ) : ℂ) *
            (⟨Real.cos γ, Real.sin γ⟩ : ℂ) *
            planeComplex (q (ix i)) := hc
      _ = candidateContactFactorPlus *
            planeComplex (q (ix i)) := by rw [hplusFactor]
  constructor
  · rw [_root_.rotation_apply, candidate_outer_start_contact_formula]
    calc
      (a : ℂ) *
          (candidateContactFactorMinus *
            planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex i))) =
          candidateContactFactorMinus *
            ((a : ℂ) * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex i))) := by ring
      _ = planeComplex (q (o (u i))) := by rw [hinnerRotation, hstartCoord]
  · rw [_root_.rotation_apply, candidate_outer_end_contact_formula]
    calc
      (a : ℂ) *
          (candidateContactFactorPlus *
            planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex i))) =
          candidateContactFactorPlus *
            ((a : ℂ) * planeComplex (Candidate.pointAtSeparationTwo
              (candidateInnerCycleIndex i))) := by ring
      _ = planeComplex (q (o (u i + 1))) := by rw [hinnerRotation, hendCoord]

/-- Every terminal representative is explicitly congruent to the candidate.
The terminal equality data exhausts the inner and boundary indices, while
the measured contact equalities determine both outer endpoints. -/
theorem terminal_component_congruent_to_candidate
    (p : FeasiblePacking15 candidateB)
    (hterminal : ¬∃ q : FeasiblePacking15 candidateB,
      ComponentBoundaryStep candidateB p q) :
    ∃ q, q ∈ connectedComponentIn (FeasibleSet15 candidateB) p.1 ∧
      CenteredCongruent15 q Candidate.pointAtSeparationTwo := by
  obtain ⟨q, hq, ix, o, u, φ, hix, ho, halt, hr, hR,
    houter, hinner, hlift, hgap, hempty, hoccupied, hphase⟩ :=
    terminal_component_actual_angular_equalities p hterminal
  have hqFeas : q ∈ FeasibleSet15 candidateB :=
    (connectedComponentIn_subset (FeasibleSet15 candidateB) p.1) hq
  obtain ⟨a, hinnerRotation⟩ :=
    exists_rotation_matching_inner_pentagon q ix φ hr hlift hgap
  have houterRotation := actual_contact_pairs_match_candidate
    q ix o u φ (fun k => polarArg (q (o k))) a hr hR
    (fun _ => rfl) hlift hphase hoccupied hinnerRotation
  let indices := actualAllIndex ix o u
  have hindices := actualAllIndex_bijective q ix o u halt hix ho hr hR
    houter hinner hqFeas
  let actualEquiv : (Fin 5 ⊕ (Fin 5 ⊕ Fin 5)) ≃ Fin 15 :=
    Equiv.ofBijective indices hindices
  let σ : Fin 15 ≃ Fin 15 := actualEquiv.symm.trans candidateAllEquiv
  have hpoint (l : Fin 5 ⊕ (Fin 5 ⊕ Fin 5)) :
      q (indices l) = planeRotation a
        (Candidate.pointAtSeparationTwo (candidateAllIndex l)) := by
    apply planeComplex_injective
    cases l with
    | inl i =>
      simpa [indices, actualAllIndex, candidateAllIndex,
        _root_.rotation_apply, planeComplex_planeRotation] using (hinnerRotation i).symm
    | inr lr =>
      cases lr with
      | inl i =>
        simpa [indices, actualAllIndex, candidateAllIndex,
          _root_.rotation_apply, planeComplex_planeRotation] using
          (houterRotation i).1.symm
      | inr i =>
        simpa [indices, actualAllIndex, candidateAllIndex,
          _root_.rotation_apply, planeComplex_planeRotation] using
          (houterRotation i).2.symm
  refine ⟨q, hq, ?_⟩
  refine ⟨σ, planeRotation a, ?_⟩
  intro j
  let l := actualEquiv.symm j
  have hactual : indices l = j := by
    exact actualEquiv.apply_symm_apply j
  have hcand : candidateAllIndex l = σ j := rfl
  simpa [hactual, hcand] using hpoint l

end CP15
