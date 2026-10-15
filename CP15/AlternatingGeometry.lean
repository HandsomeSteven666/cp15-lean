import CP15.LocalAlternatingClosed
import CP15.CyclicAngles

namespace CP15

/-- A cyclic real lift of the fifteen actual point directions. A branch
cut may occur between the last and first point; cosine differences remain
those of the actual points. -/
structure LiftedFifteenFrame (q : Fin 15 → Plane) (φ : Fin 15 → ℝ) : Prop where
  mono : StrictMono φ
  span : φ 14 - φ 0 < 2 * Real.pi
  cosine : ∀ i j,
    Real.cos (polarArg (q i) - polarArg (q j)) = Real.cos (φ i - φ j)

theorem literal_fifteen_frame (q : Fin 15 → Plane)
    (hm : StrictMono (fun i => polarArg (q i))) :
    LiftedFifteenFrame q (fun i => polarArg (q i)) := by
  refine ⟨hm, ?_, fun _ _ => rfl⟩
  linarith [(polarArg_range (q 0)).1, (polarArg_range (q 14)).2]

noncomputable def forwardArc15 (φ : Fin 15 → ℝ) (i j : Fin 15) : ℝ :=
  if i < j then φ j - φ i else φ j + 2 * Real.pi - φ i

theorem LiftedFifteenFrame.arc_nonneg {q : Fin 15 → Plane} {φ : Fin 15 → ℝ}
    (h : LiftedFifteenFrame q φ) (i j : Fin 15) : 0 ≤ forwardArc15 φ i j := by
  by_cases hij : i < j
  · simp only [forwardArc15, if_pos hij]
    linarith [h.mono hij]
  · have hi0 := h.mono.monotone (show (0 : Fin 15) ≤ i by omega)
    have hj0 := h.mono.monotone (show (0 : Fin 15) ≤ j by omega)
    have hi14 := h.mono.monotone (show i ≤ (14 : Fin 15) by omega)
    simp only [forwardArc15, if_neg hij]
    linarith [h.span]

theorem LiftedFifteenFrame.arc_cos {q : Fin 15 → Plane} {φ : Fin 15 → ℝ}
    (h : LiftedFifteenFrame q φ) (i j : Fin 15) :
    Real.cos (polarArg (q i) - polarArg (q j)) = Real.cos (forwardArc15 φ i j) := by
  rw [h.cosine]
  by_cases hij : i < j
  · simp only [forwardArc15, if_pos hij]
    rw [← Real.cos_neg (φ j - φ i)]
    congr 1
    ring
  · have heq : forwardArc15 φ i j = (φ j - φ i) + 2 * Real.pi := by
      simp only [forwardArc15, if_neg hij]
      ring
    rw [heq, Real.cos_add_two_pi, ← Real.cos_neg (φ j - φ i)]
    congr 1
    ring

/-- Pairwise distance clearance bounds every nonnegative directed angle.
If the directed arc exceeds pi the result follows from the arccos range;
otherwise cosine monotonicity checks its geometric meaning. -/
theorem directed_clearance_angle_lower (x y : Plane) (g : ℝ)
    (hx : 0 < ‖x‖) (hy : 0 < ‖y‖) (hsep : 2 ≤ dist x y) (hg : 0 ≤ g)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g) :
    contactAngle ‖x‖ ‖y‖ ≤ g := by
  by_cases hgπ : g ≤ Real.pi
  · have hd : (4 : ℝ) ≤ dist x y ^ 2 := by nlinarith [dist_nonneg (x := x) (y := y)]
    rw [dist_eq_norm, norm_sub_sq_real, polar_inner, hcos] at hd
    have hc : Real.cos g ≤ contactCos ‖x‖ ‖y‖ := by
      unfold contactCos
      apply (le_div_iff₀ (by positivity : 0 < 2 * ‖x‖ * ‖y‖)).2
      nlinarith
    have h := Real.arccos_le_arccos hc
    rw [Real.arccos_cos hg hgπ] at h
    exact h
  · exact (Real.arccos_le_pi _).trans (le_of_not_ge hgπ)

theorem contactAngle_diagonal_eq_outerAlpha (b : ℝ) (hb : 1 < b) :
    contactAngle b b = outerAlpha b := by
  have hb0 : 0 < b := by linarith
  have hr0 : 0 ≤ 1 / b := by positivity
  have hrLo : -1 ≤ 1 / b := by linarith
  have hrHi : 1 / b ≤ 1 := (div_le_one hb0).2 (by linarith)
  have hs := Real.sin_arcsin hrLo hrHi
  have hsc := Real.sin_sq_add_cos_sq (Real.arcsin (1 / b))
  rw [hs] at hsc
  have hcos : Real.cos (outerAlpha b) = 1 - 2 * (1 / b) ^ 2 := by
    have hc := Real.cos_two_mul (Real.arcsin (1 / b))
    change Real.cos (2 * Real.arcsin (1 / b)) = _
    nlinarith
  have hcontact : contactCos b b = 1 - 2 * (1 / b) ^ 2 := by
    unfold contactCos
    field_simp [ne_of_gt hb0]
    ring
  have hα0 : 0 ≤ outerAlpha b := by
    have hh : 0 ≤ Real.arcsin (1 / b) := Real.arcsin_nonneg.mpr hr0
    unfold outerAlpha
    linarith
  have hαπ : outerAlpha b ≤ Real.pi := by
    have hh := Real.arcsin_le_pi_div_two (1 / b)
    unfold outerAlpha
    linarith
  exact Real.arccos_eq_of_eq_cos hα0 hαπ (hcontact.trans hcos.symm)

/-- Two points whose radii are both close to the candidate outer radius,
and no larger than it, require at least the candidate outer angular gap.
This removes the boundary-equality assumption for an adjacent outer pair. -/
theorem candidate_outer_pair_angle_lower
    (r s : ℝ)
    (hrlo : 17 / 5 ≤ r) (hrhi : r ≤ candidateB)
    (hslo : 17 / 5 ≤ s) (hshi : s ≤ candidateB) :
    outerAlpha candidateB ≤ contactAngle r s := by
  have hB_lo : (35213 / 10000 : ℝ) ≤ candidateB :=
    candidateB_local_bounds.1.le
  have hB_hi : candidateB ≤ 35214 / 10000 :=
    candidateB_local_bounds.2.le
  have hBsmall : candidateB ≤ 18 / 5 := by linarith
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have hB0 : 0 < candidateB := by linarith
  have hrad : 0 ≤ candidateB * r - s ^ 2 + 4 := by
    have hBr : (35213 / 10000 : ℝ) * (17 / 5 : ℝ) ≤ candidateB * r :=
      calc
        (35213 / 10000 : ℝ) * (17 / 5 : ℝ) ≤ candidateB * (17 / 5 : ℝ) := by
          exact mul_le_mul_of_nonneg_right hB_lo (by norm_num)
        _ ≤ candidateB * r := by
          exact mul_le_mul_of_nonneg_left hrlo (by linarith)
    have hsSq : s ^ 2 ≤ (18 / 5 : ℝ) ^ 2 := by
      nlinarith
    nlinarith
  have hfactor1 :
      0 ≤ (candidateB - r) * (candidateB * r - s ^ 2 + 4) :=
    mul_nonneg (sub_nonneg.mpr hrhi) hrad
  have hcos1 : contactCos r s ≤ contactCos candidateB s := by
    unfold contactCos
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * r * s)
      (by positivity : 0 < 2 * candidateB * s)).2
    nlinarith [hfactor1]
  have hgap : 0 ≤ candidateB - s := sub_nonneg.mpr hshi
  have hgapSmall : candidateB - s ≤ 1 / 5 := by
    nlinarith [hB_hi, hslo]
  have hprod : candidateB * (candidateB - s) ≤
      (18 / 5 : ℝ) * (1 / 5 : ℝ) := by
    calc
      candidateB * (candidateB - s) ≤ (18 / 5 : ℝ) * (candidateB - s) :=
        mul_le_mul_of_nonneg_right hBsmall hgap
      _ ≤ (18 / 5 : ℝ) * (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hgapSmall (by norm_num)
  have hfactor2 :
      0 ≤ (candidateB - s) * (4 - candidateB * (candidateB - s)) := by
    apply mul_nonneg hgap
    nlinarith [hprod]
  have hcos2 : contactCos candidateB s ≤
      contactCos candidateB candidateB := by
    unfold contactCos
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * candidateB * s)
      (by positivity : 0 < 2 * candidateB * candidateB)).2
    nlinarith [hfactor2]
  have hcos : contactCos r s ≤ contactCos candidateB candidateB :=
    hcos1.trans hcos2
  have hangle : contactAngle candidateB candidateB ≤ contactAngle r s := by
    unfold contactAngle
    exact Real.arccos_le_arccos hcos
  rw [contactAngle_diagonal_eq_outerAlpha candidateB (by linarith)] at hangle
  exact hangle

/-- Equality in the outer-pair bound forces both endpoint radii to be the
candidate radius. The strict factors are positive throughout the stated
radial interval. -/
theorem candidate_outer_pair_angle_eq
    (r s : ℝ)
    (hrlo : 17 / 5 ≤ r) (hrhi : r ≤ candidateB)
    (hslo : 17 / 5 ≤ s) (hshi : s ≤ candidateB)
    (hangle : contactAngle r s = outerAlpha candidateB) :
    r = candidateB ∧ s = candidateB := by
  have hB_lo : (35213 / 10000 : ℝ) ≤ candidateB :=
    candidateB_local_bounds.1.le
  have hB_hi : candidateB ≤ 35214 / 10000 :=
    candidateB_local_bounds.2.le
  have hBsmall : candidateB ≤ 18 / 5 := by linarith
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have hB0 : 0 < candidateB := by linarith
  have hrad : 0 < candidateB * r - s ^ 2 + 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hrlo (by norm_num : 0 ≤ (35213 / 10000 : ℝ)),
      mul_le_mul_of_nonneg_left hslo (by norm_num : 0 ≤ (17 / 5 : ℝ))]
  have hgap : 0 ≤ candidateB - s := sub_nonneg.mpr hshi
  have hgapSmall : candidateB - s ≤ 1 / 5 := by nlinarith [hB_hi, hslo]
  have hprod : candidateB * (candidateB - s) ≤
      (18 / 5 : ℝ) * (1 / 5 : ℝ) := by
    calc
      candidateB * (candidateB - s) ≤ (18 / 5 : ℝ) * (candidateB - s) :=
        mul_le_mul_of_nonneg_right hBsmall hgap
      _ ≤ (18 / 5 : ℝ) * (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hgapSmall (by norm_num)
  have hfactor2 :
      0 ≤ (candidateB - s) * (4 - candidateB * (candidateB - s)) := by
    apply mul_nonneg hgap
    nlinarith [hprod]
  have hcos2 : contactCos candidateB s ≤
      contactCos candidateB candidateB := by
    unfold contactCos
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * candidateB * s)
      (by positivity : 0 < 2 * candidateB * candidateB)).2
    nlinarith [hfactor2]
  have hcosR : -1 ≤ contactCos r s ∧ contactCos r s ≤ 1 := by
    constructor
    · unfold contactCos
      apply (le_div_iff₀ (by positivity : 0 < 2 * r * s)).2
      nlinarith
    · unfold contactCos
      apply (div_le_iff₀ (by positivity : 0 < 2 * r * s)).2
      have hdiff : |r - s| ≤ 1 / 5 := by
        have hrl : r - s ≤ 1 / 5 := by linarith [hrhi, hslo, hB_hi]
        have hsl : s - r ≤ 1 / 5 := by linarith [hshi, hrlo, hB_hi]
        rw [abs_le]
        constructor <;> linarith
      nlinarith [sq_abs (r - s)]
  have hcosB : -1 ≤ contactCos candidateB candidateB ∧
      contactCos candidateB candidateB ≤ 1 := by
    constructor
    · unfold contactCos
      apply (le_div_iff₀ (by positivity : 0 < 2 * candidateB * candidateB)).2
      nlinarith
    · unfold contactCos
      apply (div_le_iff₀ (by positivity : 0 < 2 * candidateB * candidateB)).2
      nlinarith
  have hcosR' : Real.cos (contactAngle r s) = contactCos r s := by
    unfold contactAngle
    rw [Real.cos_arccos hcosR.1 hcosR.2]
  have hcosB' : Real.cos (outerAlpha candidateB) =
      contactCos candidateB candidateB := by
    rw [← contactAngle_diagonal_eq_outerAlpha candidateB (by linarith)]
    unfold contactAngle
    rw [Real.cos_arccos hcosB.1 hcosB.2]
  have hcosEq : contactCos r s = contactCos candidateB candidateB := by
    calc
      contactCos r s = Real.cos (contactAngle r s) := hcosR'.symm
      _ = Real.cos (outerAlpha candidateB) := by rw [hangle]
      _ = contactCos candidateB candidateB := hcosB'
  by_cases hrEq : r = candidateB
  · refine ⟨hrEq, ?_⟩
    rw [hrEq] at hcosEq
    by_contra hsEq
    have hslt : s < candidateB := lt_of_le_of_ne hshi hsEq
    have hfactor2strict :
        0 < (candidateB - s) * (4 - candidateB * (candidateB - s)) := by
      apply mul_pos (by linarith)
      nlinarith [hprod]
    have hcos2strict : contactCos candidateB s <
        contactCos candidateB candidateB := by
      unfold contactCos
      apply (div_lt_div_iff₀ (by positivity : 0 < 2 * candidateB * s)
        (by positivity : 0 < 2 * candidateB * candidateB)).2
      nlinarith [hfactor2strict]
    exact (ne_of_lt hcos2strict) hcosEq
  · have hrlt : r < candidateB := lt_of_le_of_ne hrhi hrEq
    have hfactor1 :
        0 < (candidateB - r) * (candidateB * r - s ^ 2 + 4) :=
      mul_pos (by linarith) hrad
    have hcos1strict : contactCos r s < contactCos candidateB s := by
      unfold contactCos
      apply (div_lt_div_iff₀ (by positivity : 0 < 2 * r * s)
        (by positivity : 0 < 2 * candidateB * s)).2
      nlinarith [hfactor1]
    exact False.elim (not_lt_of_ge (hcos2.trans hcosEq.symm.le) hcos1strict)

def alternatingLeft (i : Fin 5) : Fin 15 := ⟨3 * i.val, by omega⟩
def alternatingInner (i : Fin 5) : Fin 15 := ⟨3 * i.val + 1, by omega⟩
def alternatingRight (i : Fin 5) : Fin 15 := ⟨3 * i.val + 2, by omega⟩

def alternatingOuterPosition (i : Fin 5) : Fin 10 := ⟨2 * i.val, by omega⟩

def alternatingOuter (k : Fin 10) : Fin 15 :=
  if k.val % 2 = 0 then
    alternatingLeft ⟨k.val / 2, by omega⟩
  else
    alternatingRight ⟨k.val / 2, by omega⟩

theorem alternatingOuterPosition_left (i : Fin 5) :
    alternatingOuter (alternatingOuterPosition i) = alternatingLeft i := by
  fin_cases i <;> norm_num [alternatingOuter, alternatingOuterPosition,
    alternatingLeft, alternatingRight]

theorem alternatingOuterPosition_succ_right (i : Fin 5) :
    alternatingOuter (alternatingOuterPosition i + 1) = alternatingRight i := by
  fin_cases i <;> norm_num [alternatingOuter, alternatingOuterPosition,
    alternatingLeft, alternatingRight]

theorem alternating_inner_forward_arc_decomposition (φ : Fin 15 → ℝ)
    (i : Fin 5) :
    forwardArc15 φ (alternatingInner i) (alternatingInner (i + 1)) =
      forwardArc15 φ (alternatingInner i) (alternatingRight i) +
        forwardArc15 φ (alternatingRight i) (alternatingLeft (i + 1)) +
        forwardArc15 φ (alternatingLeft (i + 1)) (alternatingInner (i + 1)) := by
  fin_cases i <;> norm_num [forwardArc15, alternatingInner, alternatingRight,
    alternatingLeft] <;> ring

theorem cyclic_inner_gap_eq_forwardArc (φ : Fin 15 → ℝ) (i : Fin 5) :
    cyclicAngleGap (fun j : Fin 5 => φ (alternatingInner j)) i =
      forwardArc15 φ (alternatingInner i) (alternatingInner (i + 1)) := by
  fin_cases i <;> norm_num [cyclicAngleGap, forwardArc15, alternatingInner] <;> ring

theorem cyclic_outer_gap_eq_forwardArc (φ : Fin 15 → ℝ) (i : Fin 5) :
    cyclicAngleGap (fun k : Fin 10 => φ (alternatingOuter k))
        (alternatingOuterPosition i) =
      forwardArc15 φ (alternatingLeft i) (alternatingRight i) := by
  fin_cases i <;> norm_num [cyclicAngleGap, forwardArc15, alternatingOuter,
    alternatingOuterPosition, alternatingLeft, alternatingRight] <;> ring

/-- The angle budget is proved from the actual fifteen-point distances
and the specified alternating cyclic order. The order and local-radius
reduction still need to be supplied by the global certificate layer. -/
theorem alternating_actual_angle_budget (q : Fin 15 → Plane) (b : ℝ)
    (φ : Fin 15 → ℝ) (hframe : LiftedFifteenFrame q φ) (hsep : Separated q 2)
    (hb : 1 < b)
    (hleft : ∀ i, ‖q (alternatingLeft i)‖ = b)
    (hright : ∀ i, ‖q (alternatingRight i)‖ = b)
    (hr : ∀ i, 0 < ‖q (alternatingInner i)‖) :
    localAngularCost b (outerAlpha b) (fun i => ‖q (alternatingInner i)‖) ≤ 2 * Real.pi := by
  let r : Fin 5 → ℝ := fun i => ‖q (alternatingInner i)‖
  let a : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingLeft i) (alternatingInner i)
  let c : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingInner i) (alternatingRight i)
  let e : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingRight i) (alternatingLeft (i + 1))
  have hpair (i j : Fin 15) (hij : i ≠ j) (hi : 0 < ‖q i‖) (hj : 0 < ‖q j‖) :=
    directed_clearance_angle_lower (q i) (q j) (forwardArc15 φ i j) hi hj
      (hsep i j hij) (hframe.arc_nonneg i j) (hframe.arc_cos i j)
  have ha (i : Fin 5) : contactAngle b (r i) ≤ a i := by
    have hne : alternatingLeft i ≠ alternatingInner i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [alternatingLeft, alternatingInner] at hv
      omega
    have h := hpair (alternatingLeft i) (alternatingInner i) hne
      (by rw [hleft]; linarith) (hr i)
    simpa only [hleft] using h
  have hc (i : Fin 5) : contactAngle b (r i) ≤ c i := by
    have hne : alternatingInner i ≠ alternatingRight i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [alternatingInner, alternatingRight] at hv
      omega
    have h := hpair (alternatingInner i) (alternatingRight i) hne (hr i)
      (by rw [hright]; linarith)
    rw [hright, contactAngle_comm] at h
    exact h
  have he (i : Fin 5) : outerAlpha b ≤ e i := by
    have hne : alternatingRight i ≠ alternatingLeft (i + 1) := by
      fin_cases i <;> decide
    have h := hpair (alternatingRight i) (alternatingLeft (i + 1)) hne
      (by rw [hright]; linarith) (by rw [hleft]; linarith)
    rw [hright, hleft, contactAngle_diagonal_eq_outerAlpha b hb] at h
    exact h
  have hp (i : Fin 5) : contactAngle (r (i + 1)) (r i) ≤ c i + e i + a (i + 1) := by
    have hne : alternatingInner i ≠ alternatingInner (i + 1) := by
      fin_cases i <;> decide
    have h := hpair (alternatingInner i) (alternatingInner (i + 1)) hne (hr i) (hr (i + 1))
    have heq : forwardArc15 φ (alternatingInner i) (alternatingInner (i + 1)) =
        c i + e i + a (i + 1) := by
      fin_cases i <;> norm_num [c, e, a, forwardArc15, alternatingInner,
        alternatingLeft, alternatingRight] <;> ring
    rw [heq, contactAngle_comm] at h
    exact h
  have hturn : (∑ i, (a i + c i + e i)) = 2 * Real.pi := by
    norm_num [Fin.sum_univ_five, a, c, e, forwardArc15, alternatingLeft,
      alternatingInner, alternatingRight]
  exact angular_cost_le_turn_of_alternating_gaps b (outerAlpha b) (2 * Real.pi)
    r a c e ha hc he hp hturn

/-- The alternating angle budget remains valid when the ten outer centers
have varying radii in `[17/5, candidateB]`. Only the inner radii and cyclic
order are localized. -/
theorem alternating_actual_angle_budget_variable_outer
    (q : Fin 15 → Plane) (φ : Fin 15 → ℝ)
    (hframe : LiftedFifteenFrame q φ) (hsep : Separated q 2)
    (hleft : ∀ i, ‖q (alternatingLeft i)‖ ∈ Set.Icc (17 / 5 : ℝ) candidateB)
    (hright : ∀ i, ‖q (alternatingRight i)‖ ∈ Set.Icc (17 / 5 : ℝ) candidateB)
    (hr : ∀ i, ‖q (alternatingInner i)‖ ∈
      Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    localAngularCost candidateB (outerAlpha candidateB)
      (fun i => ‖q (alternatingInner i)‖) ≤ 2 * Real.pi := by
  let r : Fin 5 → ℝ := fun i => ‖q (alternatingInner i)‖
  let a : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingLeft i) (alternatingInner i)
  let c : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingInner i) (alternatingRight i)
  let e : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingRight i) (alternatingLeft (i + 1))
  have hpair (i j : Fin 15) (hij : i ≠ j) (hi : 0 < ‖q i‖) (hj : 0 < ‖q j‖) :=
    directed_clearance_angle_lower (q i) (q j) (forwardArc15 φ i j) hi hj
      (hsep i j hij) (hframe.arc_nonneg i j) (hframe.arc_cos i j)
  have ha (i : Fin 5) : contactAngle candidateB (r i) ≤ a i := by
    have hne : alternatingLeft i ≠ alternatingInner i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [alternatingLeft, alternatingInner] at hv
      omega
    have hactual := hpair (alternatingLeft i) (alternatingInner i) hne
      (by linarith [(hleft i).1]) (by linarith [(hr i).1])
    have hcmp := contactAngle_antitone_outer_radius
      ‖q (alternatingLeft i)‖ candidateB (r i)
      (by linarith [(hleft i).1]) (hleft i).2
      (by linarith [(hr i).1]) (by linarith [(hr i).2])
    exact hcmp.trans hactual
  have hc (i : Fin 5) : contactAngle candidateB (r i) ≤ c i := by
    have hne : alternatingInner i ≠ alternatingRight i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [alternatingInner, alternatingRight] at hv
      omega
    have hactual := hpair (alternatingInner i) (alternatingRight i) hne
      (by linarith [(hr i).1]) (by linarith [(hright i).1])
    rw [contactAngle_comm] at hactual
    have hcmp := contactAngle_antitone_outer_radius
      ‖q (alternatingRight i)‖ candidateB (r i)
      (by linarith [(hright i).1]) (hright i).2
      (by linarith [(hr i).1]) (by linarith [(hr i).2])
    exact hcmp.trans hactual
  have he (i : Fin 5) : outerAlpha candidateB ≤ e i := by
    have hne : alternatingRight i ≠ alternatingLeft (i + 1) := by
      fin_cases i <;> decide
    have hactual := hpair (alternatingRight i) (alternatingLeft (i + 1)) hne
      (by linarith [(hright i).1]) (by linarith [(hleft (i + 1)).1])
    have hbound := candidate_outer_pair_angle_lower
      ‖q (alternatingRight i)‖ ‖q (alternatingLeft (i + 1))‖
      (hright i).1 (hright i).2 (hleft (i + 1)).1 (hleft (i + 1)).2
    exact hbound.trans hactual
  have hp (i : Fin 5) : contactAngle (r (i + 1)) (r i) ≤
      c i + e i + a (i + 1) := by
    have hne : alternatingInner i ≠ alternatingInner (i + 1) := by
      fin_cases i <;> decide
    have hactual := hpair (alternatingInner i) (alternatingInner (i + 1)) hne
      (by linarith [(hr i).1]) (by linarith [(hr (i + 1)).1])
    have heq : forwardArc15 φ (alternatingInner i) (alternatingInner (i + 1)) =
        c i + e i + a (i + 1) := by
      fin_cases i <;> norm_num [c, e, a, forwardArc15, alternatingInner,
        alternatingLeft, alternatingRight] <;> ring
    rw [heq, contactAngle_comm] at hactual
    exact hactual
  have hturn : (∑ i, (a i + c i + e i)) = 2 * Real.pi := by
    norm_num [Fin.sum_univ_five, a, c, e, forwardArc15, alternatingLeft,
      alternatingInner, alternatingRight]
  exact angular_cost_le_turn_of_alternating_gaps candidateB
    (outerAlpha candidateB) (2 * Real.pi) r a c e ha hc he hp hturn

/-- In an alternating neighborhood, equality in the full turn budget forces
all five inner radii and all ten outer radii to their candidate values.
This is the local geometric rigidity statement needed before any component
or global uniqueness argument can be closed. -/
theorem local_alternating_variable_outer_rigidity
    (q : Fin 15 → Plane) (φ : Fin 15 → ℝ)
    (hframe : LiftedFifteenFrame q φ) (hsep : Separated q 2)
    (hleft : ∀ i, ‖q (alternatingLeft i)‖ ∈ Set.Icc (17 / 5 : ℝ) candidateB)
    (hright : ∀ i, ‖q (alternatingRight i)‖ ∈ Set.Icc (17 / 5 : ℝ) candidateB)
    (hr : ∀ i, ‖q (alternatingInner i)‖ ∈
      Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    (∀ i, ‖q (alternatingInner i)‖ = candidateInnerRadius) ∧
    (∀ i, ‖q (alternatingLeft i)‖ = candidateB) ∧
    (∀ i, ‖q (alternatingRight i)‖ = candidateB) ∧
    (∀ i, forwardArc15 φ (alternatingLeft i) (alternatingInner i) =
      contactAngle candidateB candidateInnerRadius) ∧
    (∀ i, forwardArc15 φ (alternatingInner i) (alternatingRight i) =
      contactAngle candidateB candidateInnerRadius) ∧
    (∀ i, forwardArc15 φ (alternatingRight i) (alternatingLeft (i + 1)) =
      outerAlpha candidateB) := by
  let r : Fin 5 → ℝ := fun i => ‖q (alternatingInner i)‖
  let a : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingLeft i) (alternatingInner i)
  let c : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingInner i) (alternatingRight i)
  let e : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingRight i) (alternatingLeft (i + 1))
  have hpair (i j : Fin 15) (hij : i ≠ j) (hi : 0 < ‖q i‖) (hj : 0 < ‖q j‖) :=
    directed_clearance_angle_lower (q i) (q j) (forwardArc15 φ i j) hi hj
      (hsep i j hij) (hframe.arc_nonneg i j) (hframe.arc_cos i j)
  have hrad := local_alternating_angle_budget_closed candidateB r
    (by linarith [candidateB_local_bounds.1]) le_rfl hr
    (alternating_actual_angle_budget_variable_outer q φ hframe hsep hleft hright hr)
  have ha (i : Fin 5) : contactAngle candidateB (r i) ≤ a i := by
    have hne : alternatingLeft i ≠ alternatingInner i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [alternatingLeft, alternatingInner] at hv
      omega
    have hactual := hpair (alternatingLeft i) (alternatingInner i) hne
      (by linarith [(hleft i).1]) (by linarith [(hr i).1])
    have hcmp := contactAngle_antitone_outer_radius
      ‖q (alternatingLeft i)‖ candidateB (r i)
      (by linarith [(hleft i).1]) (hleft i).2
      (by linarith [(hr i).1]) (by linarith [(hr i).2])
    exact hcmp.trans hactual
  have hc (i : Fin 5) : contactAngle candidateB (r i) ≤ c i := by
    have hne : alternatingInner i ≠ alternatingRight i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [alternatingInner, alternatingRight] at hv
      omega
    have hactual := hpair (alternatingInner i) (alternatingRight i) hne
      (by linarith [(hr i).1]) (by linarith [(hright i).1])
    rw [contactAngle_comm] at hactual
    have hcmp := contactAngle_antitone_outer_radius
      ‖q (alternatingRight i)‖ candidateB (r i)
      (by linarith [(hright i).1]) (hright i).2
      (by linarith [(hr i).1]) (by linarith [(hr i).2])
    exact hcmp.trans hactual
  have he (i : Fin 5) : outerAlpha candidateB ≤ e i := by
    have hne : alternatingRight i ≠ alternatingLeft (i + 1) := by
      fin_cases i <;> decide
    have hactual := hpair (alternatingRight i) (alternatingLeft (i + 1)) hne
      (by linarith [(hright i).1]) (by linarith [(hleft (i + 1)).1])
    have hbound := candidate_outer_pair_angle_lower
      ‖q (alternatingRight i)‖ ‖q (alternatingLeft (i + 1))‖
      (hright i).1 (hright i).2 (hleft (i + 1)).1 (hleft (i + 1)).2
    exact hbound.trans hactual
  have hp (i : Fin 5) : contactAngle (r (i + 1)) (r i) ≤
      c i + e i + a (i + 1) := by
    have hne : alternatingInner i ≠ alternatingInner (i + 1) := by
      fin_cases i <;> decide
    have hactual := hpair (alternatingInner i) (alternatingInner (i + 1)) hne
      (by linarith [(hr i).1]) (by linarith [(hr (i + 1)).1])
    have heq : forwardArc15 φ (alternatingInner i) (alternatingInner (i + 1)) =
        c i + e i + a (i + 1) := by
      fin_cases i <;> norm_num [c, e, a, forwardArc15, alternatingInner,
        alternatingLeft, alternatingRight] <;> ring
    rw [heq, contactAngle_comm] at hactual
    exact hactual
  have hturn : (∑ i, (a i + c i + e i)) = 2 * Real.pi := by
    norm_num [Fin.sum_univ_five, a, c, e, forwardArc15, alternatingLeft,
      alternatingInner, alternatingRight]
  obtain ⟨hbEq, hrEq, haEq, hcEq, heEq⟩ :=
    local_alternating_gaps_closed candidateB r a c e
      (by linarith [candidateB_local_bounds.1]) le_rfl hr ha hc he hp hturn
  have houterPair (i : Fin 5) :
      ‖q (alternatingRight i)‖ = candidateB ∧
        ‖q (alternatingLeft (i + 1))‖ = candidateB := by
    have hne : alternatingRight i ≠ alternatingLeft (i + 1) := by
      fin_cases i <;> decide
    have hactual := hpair (alternatingRight i) (alternatingLeft (i + 1)) hne
      (by linarith [(hright i).1]) (by linarith [(hleft (i + 1)).1])
    have hangleLower := candidate_outer_pair_angle_lower
      ‖q (alternatingRight i)‖ ‖q (alternatingLeft (i + 1))‖
      (hright i).1 (hright i).2 (hleft (i + 1)).1 (hleft (i + 1)).2
    have hangleEq : contactAngle ‖q (alternatingRight i)‖
        ‖q (alternatingLeft (i + 1))‖ = outerAlpha candidateB := by
      have heq := heEq i
      dsimp [e] at heq
      rw [heq] at hactual
      exact le_antisymm hactual hangleLower
    exact candidate_outer_pair_angle_eq
      ‖q (alternatingRight i)‖ ‖q (alternatingLeft (i + 1))‖
      (hright i).1 (hright i).2 (hleft (i + 1)).1 (hleft (i + 1)).2 hangleEq
  have hleftEq (i : Fin 5) : ‖q (alternatingLeft i)‖ = candidateB := by
    have hidx : (i - 1) + 1 = i := by fin_cases i <;> norm_num
    simpa only [hidx] using (houterPair (i - 1)).2
  refine ⟨?_, hleftEq, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [r] using hrEq i
  · intro i
    exact (houterPair i).1
  · intro i
    simpa only [a] using haEq i
  · intro i
    simpa only [c] using hcEq i
  · intro i
    simpa only [e] using heEq i

/-- A kernel-checked conclusion for the actual local alternating packing,
with no assumed angle budget, derivative estimate, or candidate identity. -/
theorem local_alternating_packing_closed (q : Fin 15 → Plane) (b : ℝ)
    (φ : Fin 15 → ℝ) (hframe : LiftedFifteenFrame q φ) (hsep : Separated q 2)
    (hb : 3 < b) (hbB : b ≤ candidateB)
    (hleft : ∀ i, ‖q (alternatingLeft i)‖ = b)
    (hright : ∀ i, ‖q (alternatingRight i)‖ = b)
    (hr : ∀ i, ‖q (alternatingInner i)‖ ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    b = candidateB ∧ ∀ i, ‖q (alternatingInner i)‖ = candidateInnerRadius := by
  have hcost := alternating_actual_angle_budget q b φ hframe hsep (by linarith)
    hleft hright (fun i => by linarith [(hr i).1])
  exact local_alternating_angle_budget_closed b (fun i => ‖q (alternatingInner i)‖)
    hb hbB hr hcost

/-- Equality in the actual fifteen-point alternating geometry.  In addition
to the optimal radius and the five inner radii, all fifteen consecutive
angular gaps are forced to equal their candidate values. -/
theorem local_alternating_packing_gap_equalities (q : Fin 15 → Plane) (b : ℝ)
    (φ : Fin 15 → ℝ) (hframe : LiftedFifteenFrame q φ) (hsep : Separated q 2)
    (hb : 3 < b) (hbB : b ≤ candidateB)
    (hleft : ∀ i, ‖q (alternatingLeft i)‖ = b)
    (hright : ∀ i, ‖q (alternatingRight i)‖ = b)
    (hr : ∀ i, ‖q (alternatingInner i)‖ ∈ Set.Icc (1697 / 1000 : ℝ) (853 / 500)) :
    b = candidateB ∧
      (∀ i, ‖q (alternatingInner i)‖ = candidateInnerRadius) ∧
      (∀ i, forwardArc15 φ (alternatingLeft i) (alternatingInner i) =
        contactAngle candidateB candidateInnerRadius) ∧
      (∀ i, forwardArc15 φ (alternatingInner i) (alternatingRight i) =
        contactAngle candidateB candidateInnerRadius) ∧
      (∀ i, forwardArc15 φ (alternatingRight i) (alternatingLeft (i + 1)) =
        outerAlpha candidateB) := by
  let r : Fin 5 → ℝ := fun i => ‖q (alternatingInner i)‖
  let a : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingLeft i) (alternatingInner i)
  let c : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingInner i) (alternatingRight i)
  let e : Fin 5 → ℝ := fun i => forwardArc15 φ (alternatingRight i) (alternatingLeft (i + 1))
  have hpair (i j : Fin 15) (hij : i ≠ j) (hi : 0 < ‖q i‖) (hj : 0 < ‖q j‖) :=
    directed_clearance_angle_lower (q i) (q j) (forwardArc15 φ i j) hi hj
      (hsep i j hij) (hframe.arc_nonneg i j) (hframe.arc_cos i j)
  have ha (i : Fin 5) : contactAngle b (r i) ≤ a i := by
    have hne : alternatingLeft i ≠ alternatingInner i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [alternatingLeft, alternatingInner] at hv
      omega
    have h := hpair (alternatingLeft i) (alternatingInner i) hne
      (by rw [hleft]; linarith) (by linarith [(hr i).1])
    simpa only [hleft] using h
  have hc (i : Fin 5) : contactAngle b (r i) ≤ c i := by
    have hne : alternatingInner i ≠ alternatingRight i := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [alternatingInner, alternatingRight] at hv
      omega
    have h := hpair (alternatingInner i) (alternatingRight i) hne
      (by linarith [(hr i).1]) (by rw [hright]; linarith)
    rw [hright, contactAngle_comm] at h
    exact h
  have he (i : Fin 5) : outerAlpha b ≤ e i := by
    have hne : alternatingRight i ≠ alternatingLeft (i + 1) := by
      fin_cases i <;> decide
    have h := hpair (alternatingRight i) (alternatingLeft (i + 1)) hne
      (by rw [hright]; linarith) (by rw [hleft]; linarith)
    rw [hright, hleft, contactAngle_diagonal_eq_outerAlpha b (by linarith)] at h
    exact h
  have hp (i : Fin 5) : contactAngle (r (i + 1)) (r i) ≤ c i + e i + a (i + 1) := by
    have hne : alternatingInner i ≠ alternatingInner (i + 1) := by
      fin_cases i <;> decide
    have h := hpair (alternatingInner i) (alternatingInner (i + 1)) hne
      (by linarith [(hr i).1]) (by linarith [(hr (i + 1)).1])
    have heq : forwardArc15 φ (alternatingInner i) (alternatingInner (i + 1)) =
        c i + e i + a (i + 1) := by
      fin_cases i <;> norm_num [c, e, a, forwardArc15, alternatingInner,
        alternatingLeft, alternatingRight] <;> ring
    rw [heq, contactAngle_comm] at h
    exact h
  have hturn : (∑ i, (a i + c i + e i)) = 2 * Real.pi := by
    norm_num [Fin.sum_univ_five, a, c, e, forwardArc15, alternatingLeft,
      alternatingInner, alternatingRight]
  exact local_alternating_gaps_closed b r a c e hb hbB hr ha hc he hp hturn

end CP15
