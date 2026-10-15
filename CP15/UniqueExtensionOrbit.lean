import CP15.UniqueExtensionGrid

namespace CP15

open scoped InnerProductSpace

set_option maxHeartbeats 0

/-- A one-step cyclic shift on each of the candidate's three five-cycles. -/
def candidateCycleNext (i : Fin 5) : Fin 5 := i + 1

theorem candidateCycleNext_bijective : Function.Bijective candidateCycleNext := by
  decide

noncomputable def candidateCycleNextEquiv : Fin 5 ≃ Fin 5 :=
  Equiv.ofBijective candidateCycleNext candidateCycleNext_bijective

def candidateCycleSumNext : Fin 5 ⊕ (Fin 5 ⊕ Fin 5) → Fin 5 ⊕ (Fin 5 ⊕ Fin 5)
  | Sum.inl i => Sum.inl (candidateCycleNext i)
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl (candidateCycleNext i))
  | Sum.inr (Sum.inr i) => Sum.inr (Sum.inr (candidateCycleNext i))

noncomputable def candidateCycleSumNextEquiv :
    (Fin 5 ⊕ (Fin 5 ⊕ Fin 5)) ≃ (Fin 5 ⊕ (Fin 5 ⊕ Fin 5)) :=
  Equiv.sumCongr candidateCycleNextEquiv
    (Equiv.sumCongr candidateCycleNextEquiv candidateCycleNextEquiv)

noncomputable def candidateShiftEquiv : Fin 15 ≃ Fin 15 :=
  (candidateAllEquiv.symm.trans candidateCycleSumNextEquiv).trans candidateAllEquiv

theorem candidateShiftEquiv_spec (z : Fin 5 ⊕ (Fin 5 ⊕ Fin 5)) :
    candidateShiftEquiv (candidateAllIndex z) =
      candidateAllIndex (candidateCycleSumNext z) := by
  change candidateAllEquiv
      (candidateCycleSumNextEquiv (candidateAllEquiv.symm (candidateAllEquiv z))) =
    candidateAllEquiv (candidateCycleSumNext z)
  rw [candidateAllEquiv.symm_apply_apply]
  cases z with
  | inl i => rfl
  | inr z' => cases z' <;> rfl

private theorem candidate_scaled_cycle_step
    (idx : Fin 5 → Fin 15)
    (hstep : ∀ i, Candidate.point (idx (i + 1)) =
      candidateRotate72 (Candidate.point (idx i))) (i : Fin 5) :
    Candidate.pointAtSeparationTwo (idx (i + 1)) =
      candidateRotate72 (Candidate.pointAtSeparationTwo (idx i)) := by
  apply planeComplex_injective
  rw [planeComplex_candidateRotate72]
  exact planeComplex_candidate_scaled_cycle idx hstep i

theorem candidateShift_moves_point (i : Fin 15) :
    Candidate.pointAtSeparationTwo (candidateShiftEquiv i) =
      candidateRotate72 (Candidate.pointAtSeparationTwo i) := by
  let z := candidateAllEquiv.symm i
  have hi : candidateAllIndex z = i := by
    change candidateAllEquiv z = i
    exact candidateAllEquiv.apply_symm_apply i
  rw [← hi, candidateShiftEquiv_spec]
  cases z with
  | inl k =>
    simpa [candidateAllIndex, candidateCycleSumNext, candidateCycleNext] using
      candidate_scaled_cycle_step candidateInnerCycleIndex
        candidate_inner_cycle_step k
  | inr z' =>
    cases z' with
    | inl k =>
      simpa [candidateAllIndex, candidateCycleSumNext, candidateCycleNext] using
        candidate_scaled_cycle_step candidateOuterStartIndex
          candidate_outer_start_cycle_step k
    | inr k =>
      simpa [candidateAllIndex, candidateCycleSumNext, candidateCycleNext] using
        candidate_scaled_cycle_step candidateOuterEndIndex
          candidate_outer_end_cycle_step k

noncomputable def candidateRotation72Circle : Circle :=
  ⟨(⟨Candidate.v, Candidate.u⟩ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [Complex.norm_def, Complex.normSq_apply]
    have hpoly : Candidate.v * Candidate.v + Candidate.u * Candidate.u = 1 := by
      nlinarith [Candidate.square_identity]
    rw [hpoly, Real.sqrt_one]⟩

theorem candidateRotate72_eq_planeRotation (x : Plane) :
    planeRotation candidateRotation72Circle x = candidateRotate72 x := by
  apply planeComplex_injective
  rw [planeComplex_planeRotation, planeComplex_candidateRotate72]
  have hcoeff : (candidateRotation72Circle : ℂ) =
      (Candidate.v : ℂ) + Candidate.u * Complex.I := by
    apply Complex.ext <;> simp [candidateRotation72Circle,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  rw [hcoeff]

noncomputable def candidateShiftIter : ℕ → Fin 15 → Fin 15
  | 0 => id
  | n + 1 => candidateShiftEquiv ∘ candidateShiftIter n

noncomputable def candidateRotationIter : ℕ → Plane ≃ₗᵢ[ℝ] Plane
  | 0 => LinearIsometryEquiv.refl ℝ Plane
  | n + 1 => (candidateRotationIter n).trans
      (planeRotation candidateRotation72Circle)

theorem candidateShiftIter_injective (n : ℕ) :
    Function.Injective (candidateShiftIter n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
    intro i j hij
    apply ih
    exact candidateShiftEquiv.injective hij

theorem candidateShiftIter_moves_point (n : ℕ) (i : Fin 15) :
    Candidate.pointAtSeparationTwo (candidateShiftIter n i) =
      candidateRotationIter n (Candidate.pointAtSeparationTwo i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [candidateShiftIter, Function.comp_apply,
      candidateRotationIter, LinearIsometryEquiv.trans_apply]
    rw [candidateShift_moves_point, ih, candidateRotate72_eq_planeRotation]

theorem candidate_point_shiftIter_unique
    (n : ℕ) (x : Plane)
    (hdisk : ‖x‖ ≤ candidateB)
    (hsep : ∀ j : Fin 15, j ≠ candidateShiftIter n 12 →
      2 ≤ dist x (Candidate.pointAtSeparationTwo j)) :
    x = Candidate.pointAtSeparationTwo (candidateShiftIter n 12) := by
  let T := candidateRotationIter n
  let y := T.symm x
  have hyDisk : ‖y‖ ≤ candidateB := by
    have hnorm : ‖y‖ = ‖x‖ := by
      dsimp [y, T]
      simpa using (candidateRotationIter n).norm_map ((candidateRotationIter n).symm x)
    rw [hnorm]
    exact hdisk
  have hysep : ∀ j : Fin 15, j ≠ 12 →
      2 ≤ dist y (Candidate.pointAtSeparationTwo j) := by
    intro j hj
    have hindices : candidateShiftIter n j ≠ candidateShiftIter n 12 := by
      intro heq
      exact hj (candidateShiftIter_injective n heq)
    have hfar := hsep (candidateShiftIter n j) hindices
    have hdist : dist y (Candidate.pointAtSeparationTwo j) =
        dist x (Candidate.pointAtSeparationTwo (candidateShiftIter n j)) := by
      calc
        dist y (Candidate.pointAtSeparationTwo j) =
            dist (T y) (T (Candidate.pointAtSeparationTwo j)) :=
              (T.dist_map y (Candidate.pointAtSeparationTwo j)).symm
        _ = dist x (Candidate.pointAtSeparationTwo (candidateShiftIter n j)) := by
          simp [T, y, candidateShiftIter_moves_point]
    exact hfar.trans_eq hdist.symm
  have hy := candidate_point12_unique_from_grid y hyDisk hysep
  have hmap := congrArg T hy
  dsimp [T, y] at hmap
  simpa [candidateShiftIter_moves_point] using hmap

theorem candidateShift_end_cycle_step (i : Fin 5) :
    candidateShiftEquiv (candidateOuterEndIndex i) =
      candidateOuterEndIndex (i + 1) := by
  have h := candidateShiftEquiv_spec (Sum.inr (Sum.inr i))
  simpa [candidateAllIndex, candidateOuterEndIndex,
    candidateCycleSumNext, candidateCycleNext] using h

theorem candidateShiftIter_end_index (i : Fin 5) :
    candidateShiftIter i.val 12 = candidateOuterEndIndex i := by
  have h0 : candidateShiftEquiv 12 = 13 := by
    simpa [candidateOuterEndIndex] using candidateShift_end_cycle_step (0 : Fin 5)
  have h1 : candidateShiftEquiv 13 = 6 := by
    simpa [candidateOuterEndIndex] using candidateShift_end_cycle_step (1 : Fin 5)
  have h2 : candidateShiftEquiv 6 = 0 := by
    simpa [candidateOuterEndIndex] using candidateShift_end_cycle_step (2 : Fin 5)
  have h3 : candidateShiftEquiv 0 = 3 := by
    simpa [candidateOuterEndIndex] using candidateShift_end_cycle_step (3 : Fin 5)
  fin_cases i
  · rfl
  · change candidateShiftEquiv 12 = 13
    exact h0
  · change candidateShiftEquiv (candidateShiftEquiv 12) = 6
    rw [h0, h1]
  · change candidateShiftEquiv (candidateShiftEquiv (candidateShiftEquiv 12)) = 0
    rw [h0, h1, h2]
  · change candidateShiftEquiv
      (candidateShiftEquiv (candidateShiftEquiv (candidateShiftEquiv 12))) = 3
    rw [h0, h1, h2, h3]

/-- The finite grid proof transfers through the fivefold rotations to all
five outer-end vertices of the candidate. -/
theorem candidate_outer_end_unique_extension (i : Fin 5) (x : Plane)
    (hdisk : ‖x‖ ≤ candidateB)
    (hsep : ∀ j : Fin 15, j ≠ candidateOuterEndIndex i →
      2 ≤ dist x (Candidate.pointAtSeparationTwo j)) :
    x = Candidate.pointAtSeparationTwo (candidateOuterEndIndex i) := by
  have hi := candidateShiftIter_end_index i
  have hsep' : ∀ j : Fin 15, j ≠ candidateShiftIter i.val 12 →
      2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
    intro j hj
    apply hsep j
    simpa [hi] using hj
  have h := candidate_point_shiftIter_unique i.val x hdisk hsep'
  simpa [hi] using h

private def candidateReflectXLinear : Plane →ₗ[ℝ] Plane where
  toFun x := !₂[x 0, -x 1]
  map_add' x y := by
    ext k
    fin_cases k <;> simp <;> ring
  map_smul' a x := by
    ext k
    fin_cases k <;> simp

private theorem plane_norm_sq_coords_aux (p : Plane) :
    ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p

noncomputable def candidateReflectXEquiv : Plane ≃ₗᵢ[ℝ] Plane := by
  let f : Plane →ₗᵢ[ℝ] Plane :=
    { candidateReflectXLinear with
      norm_map' := by
        intro x
        have hsq : ‖candidateReflectXLinear x‖ ^ 2 = ‖x‖ ^ 2 := by
          rw [plane_norm_sq_coords_aux, plane_norm_sq_coords_aux]
          simp [candidateReflectXLinear] <;> ring
        nlinarith [norm_nonneg (candidateReflectXLinear x), norm_nonneg x,
          sq_nonneg (‖candidateReflectXLinear x‖ - ‖x‖)] }
  have hfgPoint (x : Plane) : f (candidateReflectXLinear x) = x := by
    ext k
    fin_cases k <;> simp [f, candidateReflectXLinear]
  have hgfPoint (x : Plane) : candidateReflectXLinear (f x) = x := by
    ext k
    fin_cases k <;> simp [f, candidateReflectXLinear]
  have hfg : f.toLinearMap.comp candidateReflectXLinear = LinearMap.id :=
    LinearMap.ext hfgPoint
  have hgf : candidateReflectXLinear.comp f.toLinearMap = LinearMap.id :=
    LinearMap.ext hgfPoint
  exact LinearIsometryEquiv.ofLinearIsometry f candidateReflectXLinear hfg hgf

noncomputable def candidateReflection18Equiv : Plane ≃ₗᵢ[ℝ] Plane :=
  candidateReflectXEquiv.trans (planeRotation candidateRotation36Circle)

theorem candidateReflection18_apply (x : Plane) :
    candidateReflection18Equiv x =
      Candidate.pt (Candidate.c * x 0 + Candidate.s * x 1)
        (Candidate.s * x 0 - Candidate.c * x 1) := by
  calc
    candidateReflection18Equiv x =
        planeRotation candidateRotation36Circle (candidateReflectXLinear x) := rfl
    _ = candidateRotate36 (candidateReflectXLinear x) :=
      candidateRotate36_eq_planeRotation (candidateReflectXLinear x)
    _ = Candidate.pt (Candidate.c * x 0 + Candidate.s * x 1)
        (Candidate.s * x 0 - Candidate.c * x 1) := by
      ext k
      fin_cases k <;> simp [candidateRotate36, candidateReflectXLinear,
        Candidate.pt] <;> ring

def candidateReflectIndex (i : Fin 15) : Fin 15 :=
  match i.val with
  | 0 => 11
  | 1 => 13
  | 2 => 6
  | 3 => 14
  | 4 => 8
  | 5 => 10
  | 6 => 2
  | 7 => 12
  | 8 => 4
  | 9 => 9
  | 10 => 5
  | 11 => 0
  | 12 => 7
  | 13 => 1
  | 14 => 3
  | _ => 0

theorem candidateReflectIndex_bijective : Function.Bijective candidateReflectIndex := by
  decide

noncomputable def candidateReflectIndexEquiv : Fin 15 ≃ Fin 15 :=
  Equiv.ofBijective candidateReflectIndex candidateReflectIndex_bijective

theorem candidateReflection18_moves_point (i : Fin 15) :
    Candidate.pointAtSeparationTwo (candidateReflectIndex i) =
      candidateReflection18Equiv (Candidate.pointAtSeparationTwo i) := by
  have hts : Candidate.t * Candidate.s = 1 / 2 := by
    unfold Candidate.t
    field_simp [ne_of_gt Candidate.s_pos]
  have hvt : Candidate.v * Candidate.t = Candidate.t - Candidate.s := by
    have h : Candidate.t * (1 - Candidate.v) = Candidate.s := by
      calc
        Candidate.t * (1 - Candidate.v) =
            Candidate.t * (2 * Candidate.s ^ 2) := by rw [← Candidate.two_s_sq]
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
  have huv : 2 * Candidate.u * Candidate.v = Candidate.s := Candidate.two_u_v
  fin_cases i <;>
    simp [candidateReflectIndex, candidateReflection18_apply,
      Candidate.pointAtSeparationTwo, Candidate.point, Candidate.pt,
      candidateReflectXLinear] <;>
    constructor <;>
    nlinarith [Candidate.two_s_c, Candidate.two_s_v,
      Candidate.two_c_u, Candidate.two_u_v, Candidate.c_sub_v,
      Candidate.t_linear, Candidate.s_sq, Candidate.c_sq,
      Candidate.u_sq, Candidate.v_sq, Candidate.pentagon_identity,
      hus, huc, hvc, huv, hvt, hut]

theorem candidateReflection18_involutive (x : Plane) :
    candidateReflection18Equiv (candidateReflection18Equiv x) = x := by
  rw [candidateReflection18_apply, candidateReflection18_apply]
  have hcs : Candidate.c ^ 2 + Candidate.s ^ 2 = 1 := by
    nlinarith [Candidate.pentagon_identity]
  ext k
  fin_cases k
  · change Candidate.c * (Candidate.c * x 0 + Candidate.s * x 1) +
      Candidate.s * (Candidate.s * x 0 - Candidate.c * x 1) = x 0
    calc
      _ = (Candidate.c ^ 2 + Candidate.s ^ 2) * x 0 := by ring
      _ = x 0 := by rw [hcs]; ring
  · change Candidate.s * (Candidate.c * x 0 + Candidate.s * x 1) -
      Candidate.c * (Candidate.s * x 0 - Candidate.c * x 1) = x 1
    calc
      _ = (Candidate.c ^ 2 + Candidate.s ^ 2) * x 1 := by ring
      _ = x 1 := by rw [hcs]; ring

def candidateCycleNeg (i : Fin 5) : Fin 5 :=
  match i.val with
  | 0 => 0
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | _ => 0

theorem candidateReflection_end_to_start (i : Fin 5) :
    candidateReflectIndex (candidateOuterEndIndex (candidateCycleNeg i)) =
      candidateOuterStartIndex i := by
  fin_cases i <;> rfl

/-- Reflection in the candidate's 18 degree axis transfers the five
outer-end extension proofs to the five outer-start vertices. -/
theorem candidate_outer_start_unique_extension (i : Fin 5) (x : Plane)
    (hdisk : ‖x‖ ≤ candidateB)
    (hsep : ∀ j : Fin 15, j ≠ candidateOuterStartIndex i →
      2 ≤ dist x (Candidate.pointAtSeparationTwo j)) :
    x = Candidate.pointAtSeparationTwo (candidateOuterStartIndex i) := by
  let k := candidateCycleNeg i
  have htarget : candidateReflectIndex (candidateOuterEndIndex k) =
      candidateOuterStartIndex i := candidateReflection_end_to_start i
  have hyDisk : ‖candidateReflection18Equiv x‖ ≤ candidateB := by
    rw [candidateReflection18Equiv.norm_map]
    exact hdisk
  have hysep : ∀ j : Fin 15, j ≠ candidateOuterEndIndex k →
      2 ≤ dist (candidateReflection18Equiv x)
        (Candidate.pointAtSeparationTwo j) := by
    intro j hj
    have hother : candidateReflectIndex j ≠ candidateOuterStartIndex i := by
      intro hEq
      have hEq' : candidateReflectIndex j =
          candidateReflectIndex (candidateOuterEndIndex k) :=
        hEq.trans htarget.symm
      exact hj (candidateReflectIndexEquiv.injective hEq')
    have hfar := hsep (candidateReflectIndex j) hother
    have hback : candidateReflection18Equiv
        (Candidate.pointAtSeparationTwo (candidateReflectIndex j)) =
          Candidate.pointAtSeparationTwo j := by
      rw [candidateReflection18_moves_point j]
      exact candidateReflection18_involutive _
    have hdist : dist (candidateReflection18Equiv x)
        (Candidate.pointAtSeparationTwo j) =
          dist x (Candidate.pointAtSeparationTwo (candidateReflectIndex j)) := by
      calc
        dist (candidateReflection18Equiv x)
            (Candidate.pointAtSeparationTwo j) =
          dist (candidateReflection18Equiv x)
            (candidateReflection18Equiv
              (Candidate.pointAtSeparationTwo (candidateReflectIndex j))) := by
                rw [hback]
        _ = dist x (Candidate.pointAtSeparationTwo (candidateReflectIndex j)) :=
          candidateReflection18Equiv.dist_map _ _
    exact hfar.trans_eq hdist.symm
  have h := candidate_outer_end_unique_extension k
    (candidateReflection18Equiv x) hyDisk hysep
  have hback := congrArg candidateReflection18Equiv h
  rw [candidateReflection18_involutive x] at hback
  rw [← candidateReflection18_moves_point (candidateOuterEndIndex k)] at hback
  simpa [htarget] using hback

theorem candidate_inner_center_not_boundary (i : Fin 5) :
    ‖Candidate.pointAtSeparationTwo (candidateInnerCycleIndex i)‖ < candidateB := by
  rw [candidate_inner_cycle_radius]
  linarith [candidateInnerRadius_local_bounds.2, candidateB_local_bounds.1]

/-- Unconditional uniqueness of every boundary completion of the candidate:
the ten outer labels are covered by rotation and reflection, while the five
inner labels cannot satisfy the boundary premise. -/
theorem candidate_unique_boundary_extension :
    UniqueBoundaryPointFromOthers Candidate.pointAtSeparationTwo candidateB := by
  intro i hi x hx hsep
  fin_cases i
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterEndIndex 3 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterEndIndex] using hsep
    simpa [candidateOuterEndIndex] using
      candidate_outer_end_unique_extension 3 x hx hs
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterStartIndex 4 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterStartIndex] using hsep
    simpa [candidateOuterStartIndex] using
      candidate_outer_start_unique_extension 4 x hx hs
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterStartIndex 3 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterStartIndex] using hsep
    simpa [candidateOuterStartIndex] using
      candidate_outer_start_unique_extension 3 x hx hs
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterEndIndex 4 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterEndIndex] using hsep
    simpa [candidateOuterEndIndex] using
      candidate_outer_end_unique_extension 4 x hx hs
  · have hi' : ‖Candidate.pointAtSeparationTwo (candidateInnerCycleIndex 3)‖ = candidateB := by
      simpa [candidateInnerCycleIndex] using hi
    linarith [candidate_inner_center_not_boundary (3 : Fin 5)]
  · have hi' : ‖Candidate.pointAtSeparationTwo (candidateInnerCycleIndex 4)‖ = candidateB := by
      simpa [candidateInnerCycleIndex] using hi
    linarith [candidate_inner_center_not_boundary (4 : Fin 5)]
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterEndIndex 2 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterEndIndex] using hsep
    simpa [candidateOuterEndIndex] using
      candidate_outer_end_unique_extension 2 x hx hs
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterStartIndex 0 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterStartIndex] using hsep
    simpa [candidateOuterStartIndex] using
      candidate_outer_start_unique_extension 0 x hx hs
  · have hi' : ‖Candidate.pointAtSeparationTwo (candidateInnerCycleIndex 2)‖ = candidateB := by
      simpa [candidateInnerCycleIndex] using hi
    linarith [candidate_inner_center_not_boundary (2 : Fin 5)]
  · have hi' : ‖Candidate.pointAtSeparationTwo (candidateInnerCycleIndex 0)‖ = candidateB := by
      simpa [candidateInnerCycleIndex] using hi
    linarith [candidate_inner_center_not_boundary (0 : Fin 5)]
  · have hi' : ‖Candidate.pointAtSeparationTwo (candidateInnerCycleIndex 1)‖ = candidateB := by
      simpa [candidateInnerCycleIndex] using hi
    linarith [candidate_inner_center_not_boundary (1 : Fin 5)]
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterStartIndex 2 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterStartIndex] using hsep
    simpa [candidateOuterStartIndex] using
      candidate_outer_start_unique_extension 2 x hx hs
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterEndIndex 0 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterEndIndex] using hsep
    simpa [candidateOuterEndIndex] using
      candidate_outer_end_unique_extension 0 x hx hs
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterEndIndex 1 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterEndIndex] using hsep
    simpa [candidateOuterEndIndex] using
      candidate_outer_end_unique_extension 1 x hx hs
  · have hs : ∀ j : Fin 15, j ≠ candidateOuterStartIndex 1 →
        2 ≤ dist x (Candidate.pointAtSeparationTwo j) := by
      simpa [candidateOuterStartIndex] using hsep
    simpa [candidateOuterStartIndex] using
      candidate_outer_start_unique_extension 1 x hx hs

end CP15
