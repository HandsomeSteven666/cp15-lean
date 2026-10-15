import CP15.M2K9SharedOffset
import CP15.M2K9PairCorners
import CP15.M2K9SharedForcedContacts
import CP15.M2K9SharedCoreRadius
import CP15.CollisionGeometry
import CP15.PolarContact

open scoped InnerProductSpace

namespace CP15

private theorem cos_16pi_div_25_lt_neg_quarter :
    Real.cos (16 * Real.pi / 25) < (-1 / 4 : ℝ) := by
  let a : ℝ := 8 * (3141592 / 1000000) / 25
  let x : ℝ := 8 * Real.pi / 25
  have hpiLo : a < x := by
    dsimp [a, x]
    nlinarith [Real.pi_gt_d6]
  have hpiHi : x < 101 / 100 := by
    dsimp [x]
    nlinarith [Real.pi_lt_d6]
  have hx0 : 0 < x := by positivity
  have hpoly : a - a ^ 3 / 6 < x - x ^ 3 / 6 := by
    have hfac : 0 < 1 - (x ^ 2 + x * a + a ^ 2) / 6 := by
      have ha0 : 0 < a := by dsimp [a]; norm_num
      nlinarith [sq_nonneg (x - a)]
    have hid : (x - x ^ 3 / 6) - (a - a ^ 3 / 6) =
        (x - a) * (1 - (x ^ 2 + x * a + a ^ 2) / 6) := by ring
    have hdiff : 0 < (x - x ^ 3 / 6) - (a - a ^ 3 / 6) := by
      rw [hid]
      exact mul_pos (sub_pos.mpr hpiLo) hfac
    linarith
  have hsinLower : x - x ^ 3 / 6 ≤ Real.sin x :=
    Real.sin_ge_sub_cube hx0.le
  have hsin : a - a ^ 3 / 6 < Real.sin x :=
    lt_of_lt_of_le hpoly hsinLower
  have haPos : 0 < a - a ^ 3 / 6 := by
    dsimp [a]
    norm_num
  have hsinSq : (5 / 8 : ℝ) < Real.sin x ^ 2 := by
    have hbound : (5 / 8 : ℝ) < (a - a ^ 3 / 6) ^ 2 := by
      dsimp [a]
      norm_num
    have hsq : (a - a ^ 3 / 6) ^ 2 < Real.sin x ^ 2 := by
      nlinarith [sq_nonneg (Real.sin x - (a - a ^ 3 / 6)), hsin, haPos]
    linarith
  have hdouble : Real.cos (16 * Real.pi / 25) =
      1 - 2 * Real.sin x ^ 2 := by
    have hcos := Real.cos_two_mul x
    have htwo : 2 * x = 16 * Real.pi / 25 := by
      dsimp [x]
      ring
    rw [htwo] at hcos
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hdouble]
  linarith

/-- The exact contact law for a pair at distance two. The angle is a real
lift, and both possible polar lifts, including the wrap by `2*pi`, are
handled by `cos_diff_of_two_pi_lifts`. -/
private theorem shared_contact_cos_law
    (x y : Plane) (θx θy : ℝ)
    (hcosLift : Real.cos (polarArg x - polarArg y) =
      Real.cos (θy - θx))
    (hcontact : dist x y = 2) :
    2 * ‖x‖ * ‖y‖ * Real.cos (θy - θx) =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 - 4 := by
  have hdist : ‖x - y‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hcontact]
    norm_num
  rw [norm_sub_sq_real, polar_inner, hcosLift] at hdist
  nlinarith

/-- A distance-two contact from a core point to a touching-inner point in
the audited radius ranges has cosine strictly above `-1/4`. -/
private theorem shared_core_contact_cos_gt_neg_quarter
    (x y : Plane) (θx θy : ℝ)
    (hcosLift : Real.cos (polarArg x - polarArg y) =
      Real.cos (θy - θx))
    (hcontact : dist x y = 2)
    (hxlo : (27 / 25 : ℝ) ≤ ‖x‖)
    (hylo : (29 / 20 : ℝ) ≤ ‖y‖) :
    (-1 / 4 : ℝ) < Real.cos (θy - θx) := by
  have hrpos : 0 < ‖x‖ := by linarith [norm_nonneg x]
  have hspos : 0 < ‖y‖ := by linarith [norm_nonneg y]
  have hrSq : (27 / 25 : ℝ) ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxlo)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 27 / 25) (norm_nonneg x))]
  have hsSq : (29 / 20 : ℝ) ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hylo)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 29 / 20) (norm_nonneg y))]
  have hrs : (27 / 25 : ℝ) * (29 / 20 : ℝ) ≤ ‖x‖ * ‖y‖ := by
    calc
      (27 / 25 : ℝ) * (29 / 20 : ℝ) ≤ ‖x‖ * (29 / 20 : ℝ) :=
        mul_le_mul_of_nonneg_right hxlo (by norm_num)
      _ ≤ ‖x‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_left hylo (norm_nonneg x)
  have hpoly0 :
      0 < (27 / 25 : ℝ) ^ 2 +
        (27 / 25 : ℝ) * (29 / 20 : ℝ) / 2 +
        (29 / 20 : ℝ) ^ 2 - 4 := by norm_num
  have hpoly : 0 < ‖x‖ ^ 2 + ‖x‖ * ‖y‖ / 2 + ‖y‖ ^ 2 - 4 := by
    nlinarith [hrSq, hsSq, hrs]
  have hlaw := shared_contact_cos_law x y θx θy hcosLift hcontact
  have hprod : 0 < 2 * ‖x‖ * ‖y‖ *
      (Real.cos (θy - θx) + 1 / 4 : ℝ) := by
    nlinarith [hlaw, hpoly]
  have hden : 0 < 2 * ‖x‖ * ‖y‖ := by positivity
  nlinarith

private theorem shared_polar_pair_cos_reverse
    (x y : Plane) (θx θy : ℝ)
    (hxLift : θx = polarArg x ∨ θx = polarArg x + 2 * Real.pi)
    (hyLift : θy = polarArg y ∨ θy = polarArg y + 2 * Real.pi) :
    Real.cos (polarArg x - polarArg y) = Real.cos (θy - θx) := by
  calc
    Real.cos (polarArg x - polarArg y) =
        Real.cos (θx - θy) :=
      cos_diff_of_two_pi_lifts x y θx θy hxLift hyLift
    _ = Real.cos (θy - θx) := by
      rw [← neg_sub, Real.cos_neg]

private theorem shared_polar_pair_cos_direct
    (x y : Plane) (θx θy : ℝ)
    (hxLift : θx = polarArg x ∨ θx = polarArg x + 2 * Real.pi)
    (hyLift : θy = polarArg y ∨ θy = polarArg y + 2 * Real.pi) :
    Real.cos (polarArg x - polarArg y) = Real.cos (θx - θy) :=
  cos_diff_of_two_pi_lifts x y θx θy hxLift hyLift

/-- No touching center can lie in the short arc from a forced contact to
its core center, provided the forced point and the interposed point are
not both strictly high-radius. The premise is exactly the geometric class
split used below; all angular cutoffs are rational multiples of pi. -/
theorem shared_interposed_center_impossible_by_classes
    (x j k : Plane) (θx θj θk : ℝ)
    (hcosXJ : Real.cos (polarArg x - polarArg j) =
      Real.cos (θj - θx))
    (hcosXK : Real.cos (polarArg x - polarArg k) =
      Real.cos (θk - θx))
    (hcosKJ : Real.cos (polarArg k - polarArg j) =
      Real.cos (θj - θk))
    (horder₁ : θx < θk) (horder₂ : θk < θj)
    (hspan : θj - θx ≤ Real.pi)
    (hxlo : (27 / 25 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hjlo : (29 / 20 : ℝ) ≤ ‖j‖)
    (hjhi : ‖j‖ ≤ 57 / 25)
    (hklo : (29 / 20 : ℝ) ≤ ‖k‖)
    (hkhi : ‖k‖ ≤ 57 / 25)
    (hnotBothHigh : ¬ (2 < ‖j‖ ∧ 2 < ‖k‖))
    (hcontact : dist x j = 2)
    (hsepXK : 2 ≤ dist x k) (hsepKJ : 2 ≤ dist k j) : False := by
  have hgXK0 : 0 ≤ θk - θx := le_of_lt (by linarith)
  have hgXKpi : θk - θx ≤ Real.pi := by
    linarith
  have hgKJ0 : 0 ≤ θj - θk := le_of_lt (by linarith)
  have hgKJpi : θj - θk ≤ Real.pi := by
    linarith
  have hXKangle : (607 * Real.pi / 1800 : ℝ) < θk - θx := by
    by_cases hkHigh : 2 < ‖k‖
    · have hangle := shared_AH_angle_gt_60_7 x k (θk - θx)
        hxlo hxhi (by linarith) hkhi hsepXK
        hcosXK
        hgXK0 hgXKpi
      exact hangle
    · have hkhiLow : ‖k‖ ≤ 2 := le_of_not_gt hkHigh
      have hangle := shared_AL_angle_gt_70_8 x k (θk - θx)
        (by linarith [hxlo]) hxhi (by linarith [hklo]) hkhiLow hsepXK
        hcosXK
        hgXK0 hgXKpi
      have hcoeff : (607 * Real.pi / 1800 : ℝ) <
          59 * Real.pi / 150 := by
        nlinarith [Real.pi_pos]
      exact hcoeff.trans hangle
  have hKJangle : (23 * Real.pi / 75 : ℝ) < θj - θk := by
    by_cases hkHigh : 2 < ‖k‖
    · have hjLow : ‖j‖ ≤ 2 := by
        by_contra hnot
        exact False.elim (hnotBothHigh ⟨lt_of_not_ge hnot, hkHigh⟩)
      exact shared_HL_angle_gt_55_2 k j (θj - θk)
        (by linarith) hkhi hjlo hjLow hsepKJ
        hcosKJ
        hgKJ0 hgKJpi
    · have hkLow : ‖k‖ ≤ 2 := le_of_not_gt hkHigh
      by_cases hjHigh : 2 < ‖j‖
      · have hcosJK : Real.cos (polarArg j - polarArg k) =
            Real.cos (θj - θk) := by
          calc
            Real.cos (polarArg j - polarArg k) =
                Real.cos (polarArg k - polarArg j) := by
              rw [← neg_sub, Real.cos_neg]
            _ = Real.cos (θj - θk) := hcosKJ
        exact shared_HL_angle_gt_55_2 j k (θj - θk)
          (by linarith) hjhi hklo hkLow
          (by simpa [dist_comm] using hsepKJ)
          hcosJK hgKJ0 hgKJpi
      · have hjLow : ‖j‖ ≤ 2 := le_of_not_gt hjHigh
        have hangle := shared_LL_angle_ge_60 k j (θj - θk)
          (by linarith [hklo]) hkLow (by linarith [hjlo]) hjLow hsepKJ
          hcosKJ
          hgKJ0 hgKJpi
        have hcoeff : (23 * Real.pi / 75 : ℝ) < Real.pi / 3 := by
          nlinarith [Real.pi_pos]
        exact hcoeff.trans_le hangle
  have hspanLower : (16 * Real.pi / 25 : ℝ) < θj - θx := by
    have hsum : (1159 * Real.pi / 1800 : ℝ) <
        (θk - θx) + (θj - θk) := by
      nlinarith [hXKangle, hKJangle]
    have hthreshold : (16 * Real.pi / 25 : ℝ) <
        1159 * Real.pi / 1800 := by
      nlinarith [Real.pi_pos]
    have hidentity : (θk - θx) + (θj - θk) = θj - θx := by ring
    rw [hidentity] at hsum
    exact hthreshold.trans hsum
  have hcontactCos := shared_core_contact_cos_gt_neg_quarter
    x j θx θj hcosXJ hcontact hxlo hjlo
  have hT0 : 0 ≤ (16 * Real.pi / 25 : ℝ) := by positivity
  have hcosMono := Real.cos_lt_cos_of_nonneg_of_le_pi
    hT0 hspan hspanLower
  have hcosBound := cos_16pi_div_25_lt_neg_quarter
  linarith

/-- A touching-inner high-center count of two, one of which is the common
blocker, prevents two further distinct touching centers from both having
radius strictly greater than two. -/
theorem shared_not_both_other_touching_centers_high
    (p : Fin 15 → Plane) (b : ℝ) (y j k : Fin 15)
    (hcard : ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card = 2)
    (hyT : y ∈ touchingInnerSet p b)
    (hjT : j ∈ touchingInnerSet p b)
    (hkT : k ∈ touchingInnerSet p b)
    (hyHigh : 2 < ‖p y‖)
    (hyj : y ≠ j) (hyk : y ≠ k) (hjk : j ≠ k) :
    ¬ (2 < ‖p j‖ ∧ 2 < ‖p k‖) := by
  classical
  intro hBoth
  let H := (touchingInnerSet p b).filter (fun i => 2 < ‖p i‖)
  have hyH : y ∈ H := by
    simp only [H, Finset.mem_filter]
    exact ⟨hyT, hyHigh⟩
  have hjH : j ∈ H := by
    simp only [H, Finset.mem_filter]
    exact ⟨hjT, hBoth.1⟩
  have hkH : k ∈ H := by
    simp only [H, Finset.mem_filter]
    exact ⟨hkT, hBoth.2⟩
  have hsub : ({y, j, k} : Finset (Fin 15)) ⊆ H := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hyH
    · exact hjH
    · exact hkH
  have hthree : ({y, j, k} : Finset (Fin 15)).card = 3 := by
    simp [hyj, hyk, hjk]
  have hle := Finset.card_le_card hsub
  rw [hthree] at hle
  change 3 ≤ ((touchingInnerSet p b).filter
    (fun i => 2 < ‖p i‖)).card at hle
  rw [hcard] at hle
  omega

/-- Once the common blocker and one other touching-inner center account for
the two strict high-radius centers, every other touching-inner center has
radius at most `57/25`. -/
theorem shared_other_touching_radius_le_57_div_25
    (p : Fin 15 → Plane) (b : ℝ) (y z i : Fin 15)
    (hcard : ((touchingInnerSet p b).filter
      (fun t => 2 < ‖p t‖)).card = 2)
    (hyT : y ∈ touchingInnerSet p b)
    (hzT : z ∈ touchingInnerSet p b)
    (hiT : i ∈ touchingInnerSet p b)
    (hyHigh : 2 < ‖p y‖) (hzHigh : 2 < ‖p z‖)
    (hyz : y ≠ z) (hiy : i ≠ y)
    (hzhi : ‖p z‖ < 57 / 25) :
    ‖p i‖ ≤ 57 / 25 := by
  by_cases hiz : i = z
  · simpa [hiz] using hzhi.le
  · have hnotBoth := shared_not_both_other_touching_centers_high
      p b y z i hcard hyT hzT hiT hyHigh hyz hiy.symm (fun h => hiz h.symm)
    by_contra hnot
    have hcaplt : 57 / 25 < ‖p i‖ := lt_of_not_ge hnot
    have hiHigh : 2 < ‖p i‖ := by linarith
    exact hnotBoth ⟨hzHigh, hiHigh⟩

/-- Opposite cross-side signs put the blocker outside the short lifted arc
from the core point to the forced contact. This is the branch-cut-safe
orientation fact used before calling the no-interposition theorem. -/
theorem shared_blocker_lift_outside_opposite_arc
    (x y j : Plane) (θx θy θj : ℝ)
    (hxLift : θx = polarArg x ∨ θx = polarArg x + 2 * Real.pi)
    (hyLift : θy = polarArg y ∨ θy = polarArg y + 2 * Real.pi)
    (hjLift : θj = polarArg j ∨ θj = polarArg j + 2 * Real.pi)
    (hshortY : -(Real.pi) < θy - θx ∧ θy - θx < Real.pi)
    (hshortJ : 0 < θj - θx ∧ θj - θx < Real.pi)
    (hcross : planeCross x (y - x) * planeCross x (j - x) < 0) :
    θy < θx := by
  have hcx : planeCross x (y - x) = planeCross x y := by
    simp [planeCross, PiLp.sub_apply]
    ring
  have hcj : planeCross x (j - x) = planeCross x j := by
    simp [planeCross, PiLp.sub_apply]
    ring
  have hxnorm : 0 < ‖x‖ := by
    have hn : x ≠ 0 := by
      intro hzero
      subst x
      simp [planeCross] at hcross
    exact norm_pos_iff.mpr hn
  have hynorm : 0 < ‖y‖ := by
    have hn : y ≠ 0 := by
      intro hzero
      subst y
      have hzeroCross : planeCross x (0 - x) = 0 := by
        simp [planeCross, PiLp.sub_apply]
        ring
      rw [hzeroCross] at hcross
      norm_num at hcross
    exact norm_pos_iff.mpr hn
  have hjnorm : 0 < ‖j‖ := by
    have hn : j ≠ 0 := by
      intro hzero
      subst j
      have hzeroCross : planeCross x (0 - x) = 0 := by
        simp [planeCross, PiLp.sub_apply]
        ring
      rw [hzeroCross] at hcross
      norm_num at hcross
    exact norm_pos_iff.mpr hn
  have hsiny : Real.sin (θy - θx) < 0 := by
    have hycos := cos_diff_of_two_pi_lifts x y θx θy hxLift hyLift
    -- The cross/polar sine identity is expanded directly from coordinates.
    have hcrossY : planeCross x y =
        ‖x‖ * ‖y‖ * Real.sin (θy - θx) := by
      have hxc : ‖x‖ * Real.cos (polarArg x) = x 0 := by
        rw [← planeComplex_norm]
        exact Complex.norm_mul_cos_arg (planeComplex x)
      have hxs : ‖x‖ * Real.sin (polarArg x) = x 1 := by
        rw [← planeComplex_norm]
        exact Complex.norm_mul_sin_arg (planeComplex x)
      have hyc : ‖y‖ * Real.cos (polarArg y) = y 0 := by
        rw [← planeComplex_norm]
        exact Complex.norm_mul_cos_arg (planeComplex y)
      have hys : ‖y‖ * Real.sin (polarArg y) = y 1 := by
        rw [← planeComplex_norm]
        exact Complex.norm_mul_sin_arg (planeComplex y)
      rw [planeCross, ← hxc, ← hxs, ← hyc, ← hys]
      have hsin : Real.sin (θy - θx) =
          Real.sin (polarArg y - polarArg x) := by
        rcases hxLift with hxLift | hxLift <;>
          rcases hyLift with hyLift | hyLift <;>
          rw [hxLift, hyLift] <;> simp [Real.sin_sub]
      rw [hsin]
      rw [Real.sin_sub]
      ring
    have hcrossJ : planeCross x j =
        ‖x‖ * ‖j‖ * Real.sin (θj - θx) := by
      have hxc : ‖x‖ * Real.cos (polarArg x) = x 0 := by
        rw [← planeComplex_norm]
        exact Complex.norm_mul_cos_arg (planeComplex x)
      have hxs : ‖x‖ * Real.sin (polarArg x) = x 1 := by
        rw [← planeComplex_norm]
        exact Complex.norm_mul_sin_arg (planeComplex x)
      have hjc : ‖j‖ * Real.cos (polarArg j) = j 0 := by
        rw [← planeComplex_norm]
        exact Complex.norm_mul_cos_arg (planeComplex j)
      have hjs : ‖j‖ * Real.sin (polarArg j) = j 1 := by
        rw [← planeComplex_norm]
        exact Complex.norm_mul_sin_arg (planeComplex j)
      rw [planeCross, ← hxc, ← hxs, ← hjc, ← hjs]
      have hsin : Real.sin (θj - θx) =
          Real.sin (polarArg j - polarArg x) := by
        rcases hxLift with hxLift | hxLift <;>
          rcases hjLift with hjLift | hjLift <;>
          rw [hxLift, hjLift] <;> simp [Real.sin_sub]
      rw [hsin]
      rw [Real.sin_sub]
      ring
    rw [hcx, hcj, hcrossY, hcrossJ] at hcross
    have hsinJ : 0 < Real.sin (θj - θx) :=
      Real.sin_pos_of_pos_of_lt_pi hshortJ.1 hshortJ.2
    have hprod : ‖x‖ * ‖y‖ * Real.sin (θy - θx) < 0 := by
      by_contra hnot
      have hnonneg : 0 ≤ ‖x‖ * ‖y‖ * Real.sin (θy - θx) :=
        le_of_not_gt hnot
      have hJpos : 0 < ‖x‖ * ‖j‖ * Real.sin (θj - θx) := by
        positivity
      nlinarith [mul_nonneg hnonneg hJpos.le, hcross]
    have hfactor : 0 < ‖x‖ * ‖y‖ := mul_pos hxnorm hynorm
    nlinarith [hfactor, hprod]
  have hnotNonneg : ¬ 0 ≤ θy - θx := by
    intro hnonneg
    have hsinNonneg := Real.sin_nonneg_of_nonneg_of_le_pi
      hnonneg (le_of_lt hshortY.2)
    linarith
  linarith


/-- The forced opposite-side contact is the first touching-inner center on
the chosen short arc from the core point: no distinct touching center lies
strictly between. The high-radius pair exception is removed by the checked
two-center count plus the explicit `57/25` ceiling for its unique second
high center. -/
theorem shared_forced_contact_first_on_lifted_short_arc
    (p : Fin 15 → Plane) (b : ℝ) (θ : Fin 15 → ℝ)
    (hθ : ∀ i, θ i = polarArg (p i) ∨
      θ i = polarArg (p i) + 2 * Real.pi)
    (y j x : Fin 15)
    (hsep : Separated p 2)
    (hhighCard : ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card = 2)
    (hyT : y ∈ touchingInnerSet p b)
    (hjT : j ∈ touchingInnerSet p b)
    (hyHigh : 2 < ‖p y‖)
    (hzOther : ∃ z ∈ touchingInnerSet p b,
      z ≠ y ∧ 2 < ‖p z‖ ∧ ‖p z‖ < 57 / 25)
    (hjy : j ≠ y)
    (hxlo : (27 / 25 : ℝ) ≤ ‖p x‖)
    (hxhi : ‖p x‖ ≤ 1301 / 1000)
    (hjlo : ∀ i ∈ touchingInnerSet p b, (29 / 20 : ℝ) ≤ ‖p i‖)
    (hcontact : dist (p x) (p j) = 2)
    (hshortY : -Real.pi < θ y - θ x ∧ θ y - θ x < Real.pi)
    (hshortJ : 0 < θ j - θ x ∧ θ j - θ x < Real.pi)
    (hcross : planeCross (p x) (p y - p x) *
      planeCross (p x) (p j - p x) < 0) :
    ∀ k, k ∈ touchingInnerSet p b →
      θ x < θ k → θ k < θ j → False := by
  intro k hkT horder₁ horder₂
  have hyOutside := shared_blocker_lift_outside_opposite_arc
    (p x) (p y) (p j) (θ x) (θ y) (θ j)
    (hθ x) (hθ y) (hθ j) hshortY hshortJ hcross
  have hyk : y ≠ k := by
    intro heq
    subst k
    linarith
  have hjk : j ≠ k := by
    intro heq
    subst k
    linarith
  have hxk : x ≠ k := by
    intro heq
    subst k
    linarith
  obtain ⟨z, hzT, hzy, hzHigh, hzhighcap⟩ := hzOther
  have hjUpper : ‖p j‖ ≤ 57 / 25 :=
    shared_other_touching_radius_le_57_div_25 p b y z j
      hhighCard hyT hzT hjT hyHigh hzHigh hzy.symm hjy hzhighcap
  have hkUpper : ‖p k‖ ≤ 57 / 25 :=
    shared_other_touching_radius_le_57_div_25 p b y z k
      hhighCard hyT hzT hkT hyHigh hzHigh hzy.symm hyk.symm hzhighcap
  have hnotBothHigh := shared_not_both_other_touching_centers_high
    p b y j k hhighCard hyT hjT hkT hyHigh hjy.symm hyk hjk
  have hcosXJ := shared_polar_pair_cos_reverse
    (p x) (p j) (θ x) (θ j) (hθ x) (hθ j)
  have hcosXK := shared_polar_pair_cos_reverse
    (p x) (p k) (θ x) (θ k) (hθ x) (hθ k)
  have hcosKJ := shared_polar_pair_cos_reverse
    (p k) (p j) (θ k) (θ j) (hθ k) (hθ j)
  exact shared_interposed_center_impossible_by_classes
    (p x) (p j) (p k) (θ x) (θ j) (θ k)
    hcosXJ hcosXK hcosKJ horder₁ horder₂
    (by linarith [hshortJ.2])
    hxlo hxhi (hjlo j hjT) hjUpper (hjlo k hkT) hkUpper
    hnotBothHigh hcontact
    (hsep x k hxk) (hsep k j hjk.symm)

/-- First-contact form for the selected shared-blocker branch. The blocker
is on the other side of the core ray, and the checked two-high-center count
rules out the only class pair not covered by the rational angular bounds.
Thus no distinct touching-inner center can be interposed before the forced
contact on this short arc. The angle map is a single consistent choice of
polar lift for every center, so wrap-around and equality of indices are
handled without identifying different lifts of the same point. -/
theorem shared_forced_contact_has_no_interposed_touching_center
    (p : Fin 15 → Plane) (b : ℝ) (θ : Fin 15 → ℝ)
    (hθ : ∀ i, θ i = polarArg (p i) ∨
      θ i = polarArg (p i) + 2 * Real.pi)
    (y j x k : Fin 15)
    (hhighCard : ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card = 2)
    (hyT : y ∈ touchingInnerSet p b)
    (hjT : j ∈ touchingInnerSet p b)
    (hkT : k ∈ touchingInnerSet p b)
    (hyHigh : 2 < ‖p y‖)
    (hjy : j ≠ y)
    (hxlo : (27 / 25 : ℝ) ≤ ‖p x‖)
    (hxhi : ‖p x‖ ≤ 1301 / 1000)
    (hjlo : (29 / 20 : ℝ) ≤ ‖p j‖)
    (hjhi : ‖p j‖ ≤ 57 / 25)
    (hklo : (29 / 20 : ℝ) ≤ ‖p k‖)
    (hkhi : ‖p k‖ ≤ 57 / 25)
    (hcontact : dist (p x) (p j) = 2)
    (hsepXK : 2 ≤ dist (p x) (p k))
    (hsepKJ : 2 ≤ dist (p k) (p j))
    (hshortY : -Real.pi < θ y - θ x ∧ θ y - θ x < Real.pi)
    (hshortJ : 0 < θ j - θ x ∧ θ j - θ x < Real.pi)
    (hcross : planeCross (p x) (p y - p x) *
      planeCross (p x) (p j - p x) < 0)
    (horder₁ : θ x < θ k) (horder₂ : θ k < θ j)
    (hspan : θ j - θ x ≤ Real.pi) : False := by
  have hyOutside := shared_blocker_lift_outside_opposite_arc
    (p x) (p y) (p j) (θ x) (θ y) (θ j)
    (hθ x) (hθ y) (hθ j) hshortY hshortJ hcross
  have hyk : y ≠ k := by
    intro heq
    subst k
    linarith
  have hjk : j ≠ k := by
    intro heq
    subst k
    linarith
  have hnotBothHigh := shared_not_both_other_touching_centers_high
    p b y j k hhighCard hyT hjT hkT hyHigh hjy.symm hyk hjk
  have hcosXJ := shared_polar_pair_cos_reverse
    (p x) (p j) (θ x) (θ j) (hθ x) (hθ j)
  have hcosXK := shared_polar_pair_cos_reverse
    (p x) (p k) (θ x) (θ k) (hθ x) (hθ k)
  have hcosKJ := shared_polar_pair_cos_reverse
    (p k) (p j) (θ k) (θ j) (hθ k) (hθ j)
  exact shared_interposed_center_impossible_by_classes
    (p x) (p j) (p k) (θ x) (θ j) (θ k)
    hcosXJ hcosXK hcosKJ horder₁ horder₂ hspan
    hxlo hxhi hjlo hjhi hklo hkhi hnotBothHigh
    hcontact hsepXK hsepKJ

/-- The principal signed angle from `p x` to `p i`, represented by the
argument of the quotient of their complex coordinates. -/
noncomputable def sharedRelativeArg (p : Fin 15 → Plane)
    (x i : Fin 15) : ℝ :=
  Complex.arg (planeComplex (p i) / planeComplex (p x))

/-- Orient the relative angle so the forced contact lies in the positive
direction. `forward = false` reflects the principal relative angle. -/
noncomputable def sharedOrientedArg (p : Fin 15 → Plane)
    (x : Fin 15) (forward : Bool) (i : Fin 15) : ℝ :=
  if forward then sharedRelativeArg p x i else -sharedRelativeArg p x i

private theorem shared_relative_arg_im_mul_norm_sq
    (x z : Plane) (hx : planeComplex x ≠ 0) :
    (planeComplex z / planeComplex x).im *
        Complex.normSq (planeComplex x) = planeCross x z := by
  have hxPlane : x ≠ 0 := by
    intro hzero
    apply hx
    rw [hzero]
    exact Complex.ext rfl rfl
  have hnorm : 0 < Complex.normSq (planeComplex x) := by
    rw [Complex.normSq_eq_norm_sq, planeComplex_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hxPlane)
  rw [Complex.div_im]
  field_simp [ne_of_gt hnorm]
  simp only [planeComplex, planeCross]
  ring

private theorem shared_arg_pos_of_im_pos (w : ℂ) (him : 0 < w.im) :
    0 < Complex.arg w ∧ Complex.arg w < Real.pi := by
  have hnonneg : 0 ≤ Complex.arg w :=
    Complex.arg_nonneg_iff.mpr him.le
  have hpos : 0 < Complex.arg w := by
    by_contra hnot
    have hzero : Complex.arg w = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
    have hsin := Complex.norm_mul_sin_arg w
    rw [hzero, Real.sin_zero] at hsin
    linarith
  have hlt : Complex.arg w < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr (Ne.symm him.ne))
  exact ⟨hpos, hlt⟩

private theorem shared_arg_neg_of_im_neg (w : ℂ) (him : w.im < 0) :
    -Real.pi < Complex.arg w ∧ Complex.arg w < 0 := by
  exact ⟨Complex.neg_pi_lt_arg w, Complex.arg_neg_iff.mpr him⟩

private theorem shared_relative_arg_positive
    (p : Fin 15 → Plane) (x i : Fin 15)
    (hx : planeComplex (p x) ≠ 0)
    (hcross : 0 < planeCross (p x) (p i)) :
    0 < sharedRelativeArg p x i ∧
      sharedRelativeArg p x i < Real.pi := by
  have hnorm : 0 < Complex.normSq (planeComplex (p x)) := by
    have hxPlane : p x ≠ 0 := by
      intro hzero
      apply hx
      rw [hzero]
      exact Complex.ext rfl rfl
    rw [Complex.normSq_eq_norm_sq, planeComplex_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hxPlane)
  have him : 0 < (planeComplex (p i) / planeComplex (p x)).im := by
    have hid := shared_relative_arg_im_mul_norm_sq (p x) (p i) hx
    nlinarith
  exact shared_arg_pos_of_im_pos _ him

private theorem shared_relative_arg_negative
    (p : Fin 15 → Plane) (x i : Fin 15)
    (hx : planeComplex (p x) ≠ 0)
    (hcross : planeCross (p x) (p i) < 0) :
    -Real.pi < sharedRelativeArg p x i ∧
      sharedRelativeArg p x i < 0 := by
  have hnorm : 0 < Complex.normSq (planeComplex (p x)) := by
    have hxPlane : p x ≠ 0 := by
      intro hzero
      apply hx
      rw [hzero]
      exact Complex.ext rfl rfl
    rw [Complex.normSq_eq_norm_sq, planeComplex_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hxPlane)
  have him : (planeComplex (p i) / planeComplex (p x)).im < 0 := by
    have hid := shared_relative_arg_im_mul_norm_sq (p x) (p i) hx
    nlinarith
  exact shared_arg_neg_of_im_neg _ him

private theorem shared_relative_pair_cos
    (p : Fin 15 → Plane) (x i j : Fin 15)
    (hx : planeComplex (p x) ≠ 0)
    (hi : planeComplex (p i) ≠ 0)
    (hj : planeComplex (p j) ≠ 0) :
    Real.cos (polarArg (p i) - polarArg (p j)) =
      Real.cos (sharedRelativeArg p x j - sharedRelativeArg p x i) := by
  have hJ := Complex.arg_div_coe_angle hj hx
  have hI := Complex.arg_div_coe_angle hi hx
  have hangle :
      ((sharedRelativeArg p x j - sharedRelativeArg p x i : ℝ) : Real.Angle) =
        ((polarArg (p j) - polarArg (p i) : ℝ) : Real.Angle) := by
    unfold sharedRelativeArg polarArg
    rw [Real.Angle.coe_sub, hJ, hI]
    rw [Real.Angle.coe_sub]
    abel_nf
  have hcos := congrArg Real.Angle.cos hangle
  have hreal :
      Real.cos (sharedRelativeArg p x j - sharedRelativeArg p x i) =
        Real.cos (polarArg (p j) - polarArg (p i)) := by
    simpa only [Real.Angle.cos_coe] using hcos
  have hneg : polarArg (p j) - polarArg (p i) =
      -(polarArg (p i) - polarArg (p j)) := by ring
  rw [hneg, Real.cos_neg] at hreal
  exact hreal.symm

private theorem shared_oriented_pair_cos
    (p : Fin 15 → Plane) (x i j : Fin 15) (forward : Bool)
    (hx : planeComplex (p x) ≠ 0)
    (hi : planeComplex (p i) ≠ 0)
    (hj : planeComplex (p j) ≠ 0) :
    Real.cos (polarArg (p i) - polarArg (p j)) =
      Real.cos (sharedOrientedArg p x forward j -
        sharedOrientedArg p x forward i) := by
  have h := shared_relative_pair_cos p x i j hx hi hj
  cases forward with
  | true =>
      simpa [sharedOrientedArg] using h
  | false =>
      dsimp [sharedOrientedArg]
      calc
        Real.cos (polarArg (p i) - polarArg (p j)) =
            Real.cos (sharedRelativeArg p x j - sharedRelativeArg p x i) := h
        _ = Real.cos (-(sharedRelativeArg p x j -
            sharedRelativeArg p x i)) :=
          (Real.cos_neg _).symm
        _ = Real.cos ((-sharedRelativeArg p x j) -
            (-sharedRelativeArg p x i)) := by congr 1 <;> ring

private theorem shared_oriented_arg_positive
    (p : Fin 15 → Plane) (x i : Fin 15) (forward : Bool)
    (hx : planeComplex (p x) ≠ 0)
    (hsign : if forward then 0 < planeCross (p x) (p i)
      else planeCross (p x) (p i) < 0) :
    0 < sharedOrientedArg p x forward i ∧
      sharedOrientedArg p x forward i < Real.pi := by
  cases forward with
  | true =>
      have h := shared_relative_arg_positive p x i hx hsign
      simpa [sharedOrientedArg] using h
  | false =>
      have h := shared_relative_arg_negative p x i hx hsign
      dsimp [sharedOrientedArg]
      constructor <;> linarith

private theorem shared_opposite_oriented_arg_negative
    (p : Fin 15 → Plane) (x y j : Fin 15) (forward : Bool)
    (hx : planeComplex (p x) ≠ 0)
    (hJsign : if forward then 0 < planeCross (p x) (p j)
      else planeCross (p x) (p j) < 0)
    (hproduct : planeCross (p x) (p y) *
        planeCross (p x) (p j) < 0) :
    sharedOrientedArg p x forward y < 0 := by
  cases forward with
  | true =>
      simp at hJsign
      have hYsign : planeCross (p x) (p y) < 0 := by
        by_contra hnot
        have hYnonneg : 0 ≤ planeCross (p x) (p y) := le_of_not_gt hnot
        have hprodNonneg : 0 ≤
            planeCross (p x) (p y) * planeCross (p x) (p j) :=
          mul_nonneg hYnonneg hJsign.le
        exact (not_lt_of_ge hprodNonneg) hproduct
      have h := shared_relative_arg_negative p x y hx hYsign
      simpa [sharedOrientedArg] using h.2
  | false =>
      simp at hJsign
      have hYsign : 0 < planeCross (p x) (p y) := by
        by_contra hnot
        have hYnonpos : planeCross (p x) (p y) ≤ 0 := le_of_not_gt hnot
        have hprodNonneg : 0 ≤
            planeCross (p x) (p y) * planeCross (p x) (p j) :=
          mul_nonneg_of_nonpos_of_nonpos hYnonpos hJsign.le
        exact (not_lt_of_ge hprodNonneg) hproduct
      have h := shared_relative_arg_positive p x y hx hYsign
      dsimp [sharedOrientedArg]
      linarith [h.1]

private theorem shared_forced_contact_first_of_orientation
    (p : Fin 15 → Plane) (b : ℝ) (y j x : Fin 15)
    (forward : Bool)
    (hforward : if forward then
      0 < planeCross (p x) (p j) else planeCross (p x) (p j) < 0)
    (hsep : Separated p 2)
    (hhighCard : ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card = 2)
    (hyT : y ∈ touchingInnerSet p b)
    (hjT : j ∈ touchingInnerSet p b)
    (hyHigh : 2 < ‖p y‖)
    (hzOther : ∃ z ∈ touchingInnerSet p b,
      z ≠ y ∧ 2 < ‖p z‖ ∧ ‖p z‖ < 57 / 25)
    (hjy : j ≠ y)
    (hxlo : (27 / 25 : ℝ) ≤ ‖p x‖)
    (hxhi : ‖p x‖ ≤ 1301 / 1000)
    (hjlo : ∀ i ∈ touchingInnerSet p b, (29 / 20 : ℝ) ≤ ‖p i‖)
    (hcontact : dist (p x) (p j) = 2)
    (hproduct : planeCross (p x) (p y) *
      planeCross (p x) (p j) < 0) :
    ∀ k, k ∈ touchingInnerSet p b →
      0 < sharedOrientedArg p x forward k →
      sharedOrientedArg p x forward k <
        sharedOrientedArg p x forward j → False := by
  have hxPlane : p x ≠ 0 := by
    intro hzero
    rw [hzero] at hxlo
    norm_num at hxlo
  have hxC : planeComplex (p x) ≠ 0 := by
    intro hzero
    have hnorm := planeComplex_norm (p x)
    rw [hzero] at hnorm
    simp at hnorm
    linarith
  have hyPlane : p y ≠ 0 := by
    intro hzero
    rw [hzero] at hyHigh
    norm_num at hyHigh
  have hjTlow := hjlo j hjT
  have hjPlane : p j ≠ 0 := by
    intro hzero
    rw [hzero] at hjTlow
    norm_num at hjTlow
  have hjC : planeComplex (p j) ≠ 0 := by
    intro hzero
    have hnorm := planeComplex_norm (p j)
    rw [hzero] at hnorm
    simp at hnorm
    linarith
  have hyC : planeComplex (p y) ≠ 0 := by
    intro hzero
    have hnorm := planeComplex_norm (p y)
    rw [hzero] at hnorm
    simp at hnorm
    linarith
  have hthetaX : sharedOrientedArg p x forward x = 0 := by
    unfold sharedOrientedArg sharedRelativeArg
    have hdiv : planeComplex (p x) / planeComplex (p x) = 1 :=
      div_self hxC
    rw [hdiv]
    cases forward <;> simp
  have hthetaJ := shared_oriented_arg_positive p x j forward hxC hforward
  have hthetaYneg := shared_opposite_oriented_arg_negative
    p x y j forward hxC hforward hproduct
  intro k hkT hkpos hkj
  have hky : k ≠ y := by
    intro heq
    subst k
    linarith [hthetaYneg]
  have hkjne : k ≠ j := by
    intro heq
    subst k
    linarith
  have hkx : k ≠ x := by
    intro heq
    subst k
    rw [hthetaX] at hkpos
    linarith
  have hxk : x ≠ k := Ne.symm hkx
  have hjk : j ≠ k := Ne.symm hkjne
  have hkTlow := hjlo k hkT
  have hkPlane : p k ≠ 0 := by
    intro hzero
    rw [hzero] at hkTlow
    norm_num at hkTlow
  have hkC : planeComplex (p k) ≠ 0 := by
    intro hzero
    have hnorm := planeComplex_norm (p k)
    rw [hzero] at hnorm
    simp at hnorm
    linarith
  obtain ⟨z, hzT, hzy, hzHigh, hzhighcap⟩ := hzOther
  have hjUpper : ‖p j‖ ≤ 57 / 25 :=
    shared_other_touching_radius_le_57_div_25 p b y z j
      hhighCard hyT hzT hjT hyHigh hzHigh hzy.symm hjy hzhighcap
  have hkUpper : ‖p k‖ ≤ 57 / 25 :=
    shared_other_touching_radius_le_57_div_25 p b y z k
      hhighCard hyT hzT hkT hyHigh hzHigh hzy.symm hky hzhighcap
  have hnotBothHigh := shared_not_both_other_touching_centers_high
    p b y j k hhighCard hyT hjT hkT hyHigh hjy.symm hky.symm hjk
  have hcosXJ := shared_oriented_pair_cos p x x j forward hxC hxC hjC
  have hcosXK := shared_oriented_pair_cos p x x k forward hxC hxC hkC
  have hcosKJ := shared_oriented_pair_cos p x k j forward hxC hkC hjC
  have hthetaJpi :
      sharedOrientedArg p x forward j -
        sharedOrientedArg p x forward x ≤ Real.pi := by
    simpa [hthetaX] using hthetaJ.2.le
  exact shared_interposed_center_impossible_by_classes
    (p x) (p j) (p k)
    (sharedOrientedArg p x forward x)
    (sharedOrientedArg p x forward j)
    (sharedOrientedArg p x forward k)
    hcosXJ hcosXK hcosKJ
    (by rw [hthetaX]; linarith)
    (by linarith)
    hthetaJpi
    hxlo hxhi (hjlo j hjT) hjUpper hkTlow hkUpper
    hnotBothHigh hcontact
    (hsep x k hxk) (hsep k j hjk.symm)

/-- The forced opposite-side contact is the first touching-inner center in
one of the two cyclic directions. The direction is fixed by the sign of its
cross product with the core ray; the shared blocker has the opposite sign.
Angles are canonical principal quotient arguments, so this statement has
no caller-selected polar lifts or branch-cut exception. -/
theorem shared_forced_contact_first_in_cyclic_order
    (p : Fin 15 → Plane) (b : ℝ) (y j x : Fin 15)
    (hsep : Separated p 2)
    (hhighCard : ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card = 2)
    (hyT : y ∈ touchingInnerSet p b)
    (hjT : j ∈ touchingInnerSet p b)
    (hyHigh : 2 < ‖p y‖)
    (hzOther : ∃ z ∈ touchingInnerSet p b,
      z ≠ y ∧ 2 < ‖p z‖ ∧ ‖p z‖ < 57 / 25)
    (hjy : j ≠ y)
    (hxlo : (27 / 25 : ℝ) ≤ ‖p x‖)
    (hxhi : ‖p x‖ ≤ 1301 / 1000)
    (hjlo : ∀ i ∈ touchingInnerSet p b, (29 / 20 : ℝ) ≤ ‖p i‖)
    (hcontact : dist (p x) (p j) = 2)
    (hcross : planeCross (p x) (p y - p x) *
      planeCross (p x) (p j - p x) < 0) :
    ∃ forward : Bool,
      (if forward then 0 < planeCross (p x) (p j)
        else planeCross (p x) (p j) < 0) ∧
      ∀ k, k ∈ touchingInnerSet p b →
        0 < sharedOrientedArg p x forward k →
        sharedOrientedArg p x forward k <
          sharedOrientedArg p x forward j → False := by
  have hcy : planeCross (p x) (p y - p x) = planeCross (p x) (p y) := by
    simp [planeCross]
    ring
  have hcj : planeCross (p x) (p j - p x) = planeCross (p x) (p j) := by
    simp [planeCross]
    ring
  have hproduct : planeCross (p x) (p y) * planeCross (p x) (p j) < 0 := by
    rw [← hcy, ← hcj]
    exact hcross
  have hjne : planeCross (p x) (p j) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hproduct
    norm_num at hproduct
  by_cases hjpos : 0 < planeCross (p x) (p j)
  · exact ⟨true, hjpos,
      shared_forced_contact_first_of_orientation p b y j x true hjpos
        hsep hhighCard hyT hjT hyHigh hzOther hjy hxlo hxhi hjlo
        hcontact hproduct⟩
  · have hjneg : planeCross (p x) (p j) < 0 :=
      by_contra fun hnot => hjne (le_antisymm (le_of_not_gt hjpos)
        (le_of_not_gt hnot))
    exact ⟨false, hjneg,
      shared_forced_contact_first_of_orientation p b y j x false hjneg
        hsep hhighCard hyT hjT hyHigh hzOther hjy hxlo hxhi hjlo
        hcontact hproduct⟩

/-- Explicit interface between the exact two-offset bound and the
six-gap arithmetic. The premise `hcharge` is the geometric statement that
the two offsets are paid for by the wrap pair of gaps; no angle decimals or
rounded thresholds occur here. -/
theorem shared_six_gap_impossible_of_offset_support
    (s δ₁ δ₂ g₀ g₁ g₂ g₃ g₄ g₅ : ℝ)
    (hs : 2 < s) (hsD : s ≤ D candidateB)
    (hδ₁κ : δ₁ ≤ Real.arccos (2 / s))
    (hδ₂κ : δ₂ ≤ Real.arccos (2 / s))
    (hspread : Real.pi / 3 ≤ δ₁ + δ₂)
    (hsum : g₀ + g₁ + g₂ + g₃ + g₄ + g₅ = 2 * Real.pi)
    (hcharge : sharedOffset s δ₁ + sharedOffset s δ₂ ≤ g₀ + g₅)
    (hpattern :
      ((59 * Real.pi / 150 < g₁) ∧
        (23 * Real.pi / 75 < g₂) ∧
        (23 * Real.pi / 75 < g₃) ∧
        (59 * Real.pi / 150 < g₄)) ∨
      ((607 * Real.pi / 1800 < g₁) ∧
        (23 * Real.pi / 75 < g₂) ∧
        (Real.pi / 3 ≤ g₃) ∧
        (59 * Real.pi / 150 < g₄)) ∨
      ((59 * Real.pi / 150 < g₁) ∧
        (Real.pi / 3 ≤ g₂) ∧
        (23 * Real.pi / 75 < g₃) ∧
        (607 * Real.pi / 1800 < g₄))) : False := by
  have hoffset := sharedOffset_sum_gt_candidate_endpoint_of_support
    s δ₁ δ₂ hs hsD hδ₁κ hδ₂κ hspread
  exact shared_six_gap_radian_budget_impossible g₀ g₁ g₂ g₃ g₄ g₅
    hsum (lt_of_lt_of_le hoffset hcharge) hpattern

/-- The signed polar cross product in the center plane is the sine of the
oriented difference of polar arguments. -/
private theorem shared_planeCross_polar (x y : Plane) :
    planeCross x y = ‖x‖ * ‖y‖ *
      Real.sin (polarArg y - polarArg x) := by
  have hxc : ‖x‖ * Real.cos (polarArg x) = x 0 := by
    rw [← planeComplex_norm]
    exact Complex.norm_mul_cos_arg (planeComplex x)
  have hxs : ‖x‖ * Real.sin (polarArg x) = x 1 := by
    rw [← planeComplex_norm]
    exact Complex.norm_mul_sin_arg (planeComplex x)
  have hyc : ‖y‖ * Real.cos (polarArg y) = y 0 := by
    rw [← planeComplex_norm]
    exact Complex.norm_mul_cos_arg (planeComplex y)
  have hys : ‖y‖ * Real.sin (polarArg y) = y 1 := by
    rw [← planeComplex_norm]
    exact Complex.norm_mul_sin_arg (planeComplex y)
  rw [planeCross, ← hxc, ← hxs, ← hyc, ← hys]
  rw [Real.sin_sub]
  ring

/-- The relative argument based at `a` has the same oriented angular
differences as the original polar arguments. This is the sine counterpart
of `shared_relative_pair_cos`; it keeps the sign information needed for the
shared-blocker endpoint sectors. -/
private theorem shared_relative_pair_sin
    (p : Fin 15 → Plane) (a i j : Fin 15)
    (ha : planeComplex (p a) ≠ 0)
    (hi : planeComplex (p i) ≠ 0)
    (hj : planeComplex (p j) ≠ 0) :
    Real.sin (polarArg (p j) - polarArg (p i)) =
      Real.sin (sharedRelativeArg p a j - sharedRelativeArg p a i) := by
  have hJ := Complex.arg_div_coe_angle hj ha
  have hI := Complex.arg_div_coe_angle hi ha
  have hangle :
      ((sharedRelativeArg p a j - sharedRelativeArg p a i : ℝ) : Real.Angle) =
        ((polarArg (p j) - polarArg (p i) : ℝ) : Real.Angle) := by
    unfold sharedRelativeArg polarArg
    rw [Real.Angle.coe_sub, hJ, hI]
    rw [Real.Angle.coe_sub]
    abel_nf
  have hsin := congrArg Real.Angle.sin hangle
  simpa only [Real.Angle.sin_coe] using hsin.symm

/-- Contact-vector angle measured from the inward radial direction. The
definition is tied to the actual blocker and target centers. -/
noncomputable def sharedContactDelta (s : ℝ) (y x : Plane) : ℝ :=
  Real.arccos (-⟪y, x - y⟫_ℝ / (2 * s))

/-- A strict shared-blocker contact determines a genuine contact-vector
angle in `(0, arccos (2/s))`. The nonzero-cross premise is exactly the
opposite-side fact for the two targets; it rules out the radial endpoint. -/
theorem shared_contact_delta_domain
    (x y : Plane) (s : ℝ)
    (hs : 2 < s) (hy : ‖y‖ = s)
    (hcontact : dist x y = 2)
    (hblock : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ)
    (hcross : planeCross y x ≠ 0) :
    0 < sharedContactDelta s y x ∧
      sharedContactDelta s y x < Real.arccos (2 / s) ∧
      2 * s * Real.cos (sharedContactDelta s y x) =
        -⟪y, x - y⟫_ℝ := by
  let w := x - y
  have hwnorm : ‖w‖ = 2 := by
    dsimp [w]
    rw [← dist_eq_norm]
    exact hcontact
  have hcrossw : planeCross y w = planeCross y x := by
    dsimp [w]
    simp [planeCross, PiLp.sub_apply]
    ring
  have hcrosswnz : planeCross y w ≠ 0 := by
    rw [hcrossw]
    exact hcross
  have hinnerlt : ⟪y, w⟫_ℝ < -4 := by
    dsimp [w]
    exact strict_contact_vector_inner_lt_neg_four x y hcontact hblock
  have hgram := plane_dot_cross_identity y w w
  rw [real_inner_self_eq_norm_sq, hwnorm, hy] at hgram
  have hcrosssq : 0 < planeCross y w ^ 2 := sq_pos_of_ne_zero hcrosswnz
  have hinnerabs := abs_real_inner_le_norm y w
  rw [hy, hwnorm] at hinnerabs
  have harglo :
      (2 / s : ℝ) < -⟪y, w⟫_ℝ / (2 * s) := by
    apply (div_lt_div_iff₀ (by linarith : (0 : ℝ) < s)
      (by positivity : (0 : ℝ) < 2 * s)).2
    have h4s : 4 * s < -⟪y, w⟫_ℝ * s :=
      mul_lt_mul_of_pos_right (by linarith : (4 : ℝ) < -⟪y, w⟫_ℝ)
        (by linarith : (0 : ℝ) < s)
    nlinarith
  have hargupper :
      -⟪y, w⟫_ℝ / (2 * s) < 1 := by
    have hinnerSq : ⟪y, w⟫_ℝ ^ 2 < 4 * s ^ 2 := by
      nlinarith [hgram]
    have hneg : ⟪y, w⟫_ℝ < 0 := by linarith
    apply (div_lt_one (by positivity : (0 : ℝ) < 2 * s)).2
    nlinarith
  have hsarg : -1 ≤ -⟪y, w⟫_ℝ / (2 * s) := by
    have hpos : 0 < 2 / s := by positivity
    linarith
  have hargcos : Real.cos (sharedContactDelta s y x) =
      -⟪y, w⟫_ℝ / (2 * s) := by
    unfold sharedContactDelta
    exact Real.cos_arccos hsarg hargupper.le
  have hδpos : 0 < sharedContactDelta s y x := by
    unfold sharedContactDelta
    exact Real.arccos_pos.mpr hargupper
  have hδupper : sharedContactDelta s y x < Real.arccos (2 / s) := by
    unfold sharedContactDelta
    have hspos : 0 < s := by linarith
    have hratio : 0 ≤ 2 / s := by positivity
    have hbase : -1 ≤ 2 / s := by linarith
    exact Real.arccos_lt_arccos hbase harglo hargupper.le
  refine ⟨hδpos, hδupper, ?_⟩
  rw [hargcos]
  dsimp [w]
  field_simp

/-- If a distance-two target has contact-vector angle `δ`, then its
unsigned polar separation from the blocker is exactly `sharedOffset`.
The hypotheses `hcos` and `hsinAbs` are the standard polar-coordinate
identities for the displayed actual angle `θ`. -/
theorem sharedOffset_eq_short_polar_angle
    (x y : Plane) (s δ θ : ℝ)
    (hs : 2 < s) (hy : ‖y‖ = s)
    (hcontact : dist x y = 2)
    (hdelta : 2 * s * Real.cos δ = -⟪y, x - y⟫_ℝ)
    (hδpos : 0 < δ) (hθpos : 0 < θ)
    (hδlt : δ < Real.pi / 2) (hθlt : θ < Real.pi / 2)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos θ)
    (hsinAbs : |Real.sin (polarArg x - polarArg y)| = Real.sin θ) :
    sharedOffset s δ = θ := by
  have hwnorm : ‖x - y‖ = 2 := by
    rw [← dist_eq_norm]
    exact hcontact
  have hdot : ⟪y, x⟫_ℝ = s ^ 2 - 2 * s * Real.cos δ := by
    have hsub : ⟪y, x - y⟫_ℝ = ⟪y, x⟫_ℝ - s ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq, hy]
    rw [hsub] at hdelta
    nlinarith
  have hcrossSub : planeCross y (x - y) = planeCross y x := by
    simp [planeCross, PiLp.sub_apply]
    ring
  have hgram := plane_dot_cross_identity y (x - y) (x - y)
  rw [real_inner_self_eq_norm_sq, hwnorm, hy] at hgram
  have hcrossSq : (planeCross y x) ^ 2 = (2 * s * Real.sin δ) ^ 2 := by
    rw [hcrossSub] at hgram
    have hinner : ⟪y, x - y⟫_ℝ = -(2 * s * Real.cos δ) := by linarith
    rw [hinner] at hgram
    have hsin := Real.sin_sq_add_cos_sq δ
    nlinarith [hsin]
  have hsinδpos : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith [Real.pi_pos])
  have hcrossAbs : |planeCross y x| = 2 * s * Real.sin δ := by
    have habsSq : |planeCross y x| ^ 2 =
        (2 * s * Real.sin δ) ^ 2 := by simpa [sq_abs] using hcrossSq
    have habsNonneg : 0 ≤ |planeCross y x| := abs_nonneg _
    have hrightNonneg : 0 ≤ 2 * s * Real.sin δ := by positivity
    nlinarith
  have hdotPolar : ⟪y, x⟫_ℝ = ‖x‖ * s * Real.cos θ := by
    calc
      ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := real_inner_comm _ _
      _ = ‖x‖ * ‖y‖ * Real.cos (polarArg x - polarArg y) := polar_inner x y
      _ = ‖x‖ * s * Real.cos θ := by rw [hy, hcos]
  have hcrossPolar : planeCross y x =
      ‖y‖ * ‖x‖ * Real.sin (polarArg x - polarArg y) :=
    shared_planeCross_polar y x
  have hcrossAbsPolar : |planeCross y x| = s * ‖x‖ * Real.sin θ := by
    calc
      |planeCross y x| =
          |‖y‖ * ‖x‖ * Real.sin (polarArg x - polarArg y)| := by
        rw [hcrossPolar]
      _ = ‖y‖ * ‖x‖ *
          |Real.sin (polarArg x - polarArg y)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg y),
          abs_of_nonneg (norm_nonneg x)]
      _ = s * ‖x‖ * Real.sin θ := by rw [hsinAbs, hy]
  have hxpos : 0 < ‖x‖ := by
    by_contra hnot
    have hxzero : x = 0 := norm_eq_zero.mp
      (le_antisymm (le_of_not_gt hnot) (norm_nonneg _))
    have hdist : dist x y = ‖y‖ := by
      rw [dist_eq_norm]
      simp [hxzero]
    rw [hcontact, hy] at hdist
    linarith [hs]
  have hscaleCos : ‖x‖ * Real.cos θ = s - 2 * Real.cos δ := by
    have hspos : 0 < s := by linarith
    nlinarith [hdot, hdotPolar]
  have hscaleSin : ‖x‖ * Real.sin θ = 2 * Real.sin δ := by
    have hspos : 0 < s := by linarith
    nlinarith [hcrossAbs, hcrossAbsPolar]
  have hcosPos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθlt⟩
  have hdenPos : 0 < s - 2 * Real.cos δ := by
    have hcosle := Real.cos_le_one δ
    have hspos : 0 < s := by linarith
    linarith
  have hquot : Real.sin θ / Real.cos θ =
      (2 * Real.sin δ) / (s - 2 * Real.cos δ) := by
    calc
      Real.sin θ / Real.cos θ =
          (‖x‖ * Real.sin θ) / (‖x‖ * Real.cos θ) := by
        field_simp [ne_of_gt hxpos, ne_of_gt hcosPos]
      _ = (2 * Real.sin δ) / (s - 2 * Real.cos δ) := by
        rw [hscaleSin, hscaleCos]
  have htan : Real.tan θ =
      (2 * Real.sin δ) / (s - 2 * Real.cos δ) := by
    rw [Real.tan_eq_sin_div_cos]
    exact hquot
  unfold sharedOffset
  rw [← htan]
  exact Real.arctan_tan (by linarith) hθlt

/-- The actual blocker contact's polar offset equals `sharedOffset` of its
contact-vector angle. All angle data here comes from the two center vectors;
no gap-charge hypothesis occurs. -/
theorem shared_actual_contact_offset_eq
    (p : Fin 15 → Plane) (x y : Fin 15) (s : ℝ)
    (hs : 2 < s) (hy : ‖p y‖ = s)
    (hcontact : dist (p x) (p y) = 2)
    (hblock : ‖p x‖ ^ 2 < ⟪p y, p x⟫_ℝ)
    (hcross : planeCross (p y) (p x) ≠ 0) :
    sharedOffset s (sharedContactDelta s (p y) (p x)) =
      |sharedRelativeArg p y x| := by
  let δ := sharedContactDelta s (p y) (p x)
  let α := sharedRelativeArg p y x
  have hδ := shared_contact_delta_domain (p x) (p y) s
    hs hy hcontact hblock hcross
  have hyC : planeComplex (p y) ≠ 0 := by
    intro hz
    have hnorm := planeComplex_norm (p y)
    rw [hz] at hnorm
    simp at hnorm
    linarith
  have hxC : planeComplex (p x) ≠ 0 := by
    intro hz
    have hn : ‖p x‖ = 0 := by
      rw [← planeComplex_norm, hz]
      simp
    have hxzero : p x = 0 := norm_eq_zero.mp hn
    have hdist : dist (p x) (p y) = ‖p y‖ := by
      rw [dist_eq_norm]
      simp [hxzero]
    rw [hcontact, hy] at hdist
    linarith [hs]
  have hαself : sharedRelativeArg p y y = 0 := by
    unfold sharedRelativeArg
    exact Complex.arg_div_self _
  have hcosRel := shared_relative_pair_cos p y y x hyC hyC hxC
  have hcosLift :
      Real.cos (polarArg (p x) - polarArg (p y)) = Real.cos α := by
    have h := hcosRel
    rw [hαself, sub_zero] at h
    calc
      Real.cos (polarArg (p x) - polarArg (p y)) =
          Real.cos (polarArg (p y) - polarArg (p x)) := by
        rw [show polarArg (p x) - polarArg (p y) =
          -(polarArg (p y) - polarArg (p x)) by ring, Real.cos_neg]
      _ = Real.cos α := by simpa [α] using h
  have hsinRel := shared_relative_pair_sin p y y x hyC hyC hxC
  have hsinLift :
      Real.sin (polarArg (p x) - polarArg (p y)) = Real.sin α := by
    rw [hαself, sub_zero] at hsinRel
    simpa [α] using hsinRel
  have hθpos : 0 < |α| := by
    have hne : α ≠ 0 := by
      intro hz
      have hsin := hsinLift
      rw [hz, Real.sin_zero] at hsin
      have hcrossEq := shared_planeCross_polar (p y) (p x)
      rw [hsin] at hcrossEq
      simp at hcrossEq
      exact hcross hcrossEq
    exact abs_pos.mpr hne
  have hθlt : |α| < Real.pi / 2 := by
    have hdot : 0 < ⟪p y, p x⟫_ℝ := by
      have hxpos : 0 < ‖p x‖ := by
        by_contra hnot
        have hxzero : p x = 0 := norm_eq_zero.mp
          (le_antisymm (le_of_not_gt hnot) (norm_nonneg _))
        have hdist : dist (p x) (p y) = ‖p y‖ := by
          rw [dist_eq_norm]
          simp [hxzero]
        rw [hcontact, hy] at hdist
        linarith [hs]
      exact lt_trans (sq_pos_of_pos hxpos) hblock
    have hreal :
        (planeComplex (p x) / planeComplex (p y)).re *
          Complex.normSq (planeComplex (p y)) = ⟪p y, p x⟫_ℝ := by
      rw [Complex.div_re]
      have hnorm : Complex.normSq (planeComplex (p y)) ≠ 0 := by
        rw [Complex.normSq_eq_norm_sq, planeComplex_norm]
        exact ne_of_gt (sq_pos_of_pos (by linarith : 0 < ‖p y‖))
      field_simp [hnorm]
      simp [planeComplex, PiLp.inner_apply, Fin.sum_univ_two]
    have hnormSq : 0 < Complex.normSq (planeComplex (p y)) := by
      rw [Complex.normSq_eq_norm_sq, planeComplex_norm]
      exact sq_pos_of_pos (by linarith : 0 < ‖p y‖)
    have hre : 0 < (planeComplex (p x) / planeComplex (p y)).re := by
      apply (mul_pos_iff_of_pos_right hnormSq).mp
      rw [hreal]
      exact hdot
    have harg : |Complex.arg
        (planeComplex (p x) / planeComplex (p y))| < Real.pi / 2 := by
      exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    simpa [α, sharedRelativeArg] using harg
  have hcosAbs : Real.cos (polarArg (p x) - polarArg (p y)) =
      Real.cos |α| := by
    rw [Real.cos_abs]
    exact hcosLift
  have hsinAbs : |Real.sin (polarArg (p x) - polarArg (p y))| =
      Real.sin |α| := by
    rw [hsinLift]
    have hαrange : |α| ≤ Real.pi := by
      exact hθlt.le.trans (by linarith [Real.pi_pos])
    exact Real.abs_sin_eq_sin_abs_of_abs_le_pi hαrange
  have hoffset := sharedOffset_eq_short_polar_angle
    (p x) (p y) s δ |α| hs hy hcontact hδ.2.2
    hδ.1 hθpos
    (hδ.2.1.trans (Real.arccos_lt_pi_div_two.mpr (by positivity)))
    hθlt hcosAbs hsinAbs
  simpa [δ, α] using hoffset

/-- When the blocker radius squared is greater than `16/3`, every
distance-two target lies in an open `π/3` polar sector about the blocker.
This is an exact quadratic estimate: the contact cosine numerator exceeds
the half-angle threshold by `(r-s/2)^2 + 3s^2/4 - 4`. -/
theorem shared_blocker_target_sector_lt_pi_div_three
    (p : Fin 15 → Plane) (anchor target : Fin 15)
    (hysq : (16 / 3 : ℝ) < ‖p anchor‖ ^ 2)
    (hcontact : dist (p target) (p anchor) = 2) :
    |sharedRelativeArg p anchor target| < Real.pi / 3 := by
  let s := ‖p anchor‖
  let r := ‖p target‖
  have hs : 2 < s := by
    dsimp [s]
    have hn := norm_nonneg (p anchor)
    nlinarith
  have hrpos : 0 < r := by
    dsimp [r]
    by_contra hnot
    have hz : p target = 0 := norm_eq_zero.mp
      (le_antisymm (le_of_not_gt hnot) (norm_nonneg _))
    have hdist : dist (p target) (p anchor) = ‖p anchor‖ := by
      rw [dist_eq_norm]
      simp [hz]
    rw [hcontact] at hdist
    dsimp [s] at hs
    linarith
  have hcontactFormula :
      2 * ⟪p anchor, p target⟫_ℝ = r ^ 2 + s ^ 2 - 4 := by
    have hsq : ‖p target - p anchor‖ ^ 2 = 4 := by
      rw [← dist_eq_norm, hcontact]
      norm_num
    rw [norm_sub_sq_real] at hsq
    dsimp [r, s]
    nlinarith [real_inner_comm (p target) (p anchor)]
  have hmargin : 0 < r ^ 2 - s * r + s ^ 2 - 4 := by
    have hsq : 0 ≤ (r - s / 2) ^ 2 := sq_nonneg _
    have hsMargin : 0 < 3 * s ^ 2 / 4 - 4 := by nlinarith [hysq]
    nlinarith
  have hdotOver : (1 / 2 : ℝ) <
      ⟪p anchor, p target⟫_ℝ / (s * r) := by
    have hden : 0 < s * r := mul_pos (by linarith) hrpos
    have hnum : s * r < 2 * ⟪p anchor, p target⟫_ℝ := by
      rw [hcontactFormula]
      dsimp [r, s] at hmargin ⊢
      nlinarith [hmargin]
    apply (lt_div_iff₀ hden).2
    nlinarith [hnum]
  have hyC : planeComplex (p anchor) ≠ 0 := by
    intro hz
    have hn : ‖p anchor‖ = 0 := by
      rw [← planeComplex_norm, hz]
      simp
    dsimp [s] at hs
    rw [hn] at hs
    norm_num at hs
  have htC : planeComplex (p target) ≠ 0 := by
    intro hz
    have hn : ‖p target‖ = 0 := by
      rw [← planeComplex_norm, hz]
      simp
    dsimp [r] at hrpos
    rw [hn] at hrpos
    norm_num at hrpos
  have hαself : sharedRelativeArg p anchor anchor = 0 := by
    unfold sharedRelativeArg
    exact Complex.arg_div_self _
  have hcosRel := shared_relative_pair_cos p anchor anchor target
    hyC hyC htC
  have hcosα : Real.cos (sharedRelativeArg p anchor target) =
      ⟪p anchor, p target⟫_ℝ / (s * r) := by
    have hpolar := polar_inner (p anchor) (p target)
    have hcosid : Real.cos (polarArg (p anchor) - polarArg (p target)) =
        Real.cos (sharedRelativeArg p anchor target) := by
      simpa [hαself] using hcosRel
    rw [hcosid] at hpolar
    have hden : ‖p anchor‖ * ‖p target‖ ≠ 0 :=
      ne_of_gt (mul_pos (by linarith) hrpos)
    have hanchorNorm : ‖p anchor‖ ≠ 0 := ne_of_gt (by linarith)
    have htargetNorm : ‖p target‖ ≠ 0 := ne_of_gt hrpos
    dsimp [s, r]
    rw [hpolar]
    field_simp [hden, hanchorNorm, htargetNorm]
  have hcosAbs : (1 / 2 : ℝ) <
      Real.cos |sharedRelativeArg p anchor target| := by
    rw [Real.cos_abs]
    exact hdotOver.trans_eq hcosα.symm
  have hαrange : |sharedRelativeArg p anchor target| ≤ Real.pi := by
    unfold sharedRelativeArg
    apply abs_le.mpr
    exact ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
  by_contra hnot
  have hlarge : Real.pi / 3 ≤ |sharedRelativeArg p anchor target| :=
    le_of_not_gt hnot
  have hcosle := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ Real.pi / 3) hαrange hlarge
  rw [Real.cos_pi_div_three] at hcosle
  linarith

/-- No touching center can lie strictly inside the short angular sector
between a target and its blocker when the target-target support and the
checked `A-H`/`A-L` angle bounds apply. The sector orientation is explicit,
so this covers both sides of the polar branch cut. -/
theorem shared_no_touching_center_in_target_sector
    (p : Fin 15 → Plane) (anchor target k : Fin 15)
    (hsep : Separated p 2) (hne : target ≠ k)
    (hanchor : p anchor ≠ 0)
    (htlo : (27 / 25 : ℝ) ≤ ‖p target‖)
    (hthi : ‖p target‖ ≤ 1301 / 1000)
    (hklo : (29 / 20 : ℝ) ≤ ‖p k‖)
    (hkhi : ‖p k‖ ≤ 57 / 25)
    (hαlt : |sharedRelativeArg p anchor target| < Real.pi / 3)
    (hsector :
      (0 < sharedRelativeArg p anchor target ∧
        0 < sharedRelativeArg p anchor k ∧
        sharedRelativeArg p anchor k < sharedRelativeArg p anchor target) ∨
      (sharedRelativeArg p anchor target < 0 ∧
        sharedRelativeArg p anchor target < sharedRelativeArg p anchor k ∧
        sharedRelativeArg p anchor k < 0)) : False := by
  have htC : planeComplex (p target) ≠ 0 := by
    intro hz
    have hn : ‖p target‖ = 0 := by
      rw [← planeComplex_norm, hz]
      simp
    rw [hn] at htlo
    norm_num at htlo
  have hkC : planeComplex (p k) ≠ 0 := by
    intro hz
    have hn : ‖p k‖ = 0 := by
      rw [← planeComplex_norm, hz]
      simp
    rw [hn] at hklo
    norm_num at hklo
  have hpair := shared_relative_pair_cos p anchor target k
    (by
      intro hz
      have hn : ‖p anchor‖ = 0 := by
        rw [← planeComplex_norm, hz]
        simp
      exact hanchor (norm_eq_zero.mp hn))
    htC hkC
  rcases hsector with hpos | hneg
  · let g := sharedRelativeArg p anchor target -
      sharedRelativeArg p anchor k
    have hg0 : 0 < g := by dsimp [g]; linarith
    have hglt : g < Real.pi / 3 := by
      dsimp [g]
      have hbound := abs_lt.mp hαlt
      linarith [hbound.2, hpos.2.2]
    have hcos : Real.cos (polarArg (p target) - polarArg (p k)) =
        Real.cos g := by
      rw [hpair]
      rw [show sharedRelativeArg p anchor k -
          sharedRelativeArg p anchor target = -g by dsimp [g]; ring,
        Real.cos_neg]
    by_cases hkh : 2 < ‖p k‖
    · have hangle := shared_AH_angle_gt_60_7 (p target) (p k) g
        htlo hthi hkh.le hkhi (hsep target k hne) hcos hg0.le
        (hglt.le.trans (by nlinarith [Real.pi_pos]))
      have hthreshold : Real.pi / 3 < 607 * Real.pi / 1800 := by
        nlinarith [Real.pi_pos]
      linarith
    · have hkhiLow : ‖p k‖ ≤ 2 := le_of_not_gt hkh
      have htloLow : (699 / 1000 : ℝ) ≤ ‖p target‖ := by
        norm_num at htlo ⊢ <;> linarith
      have hangle := shared_AL_angle_gt_70_8 (p target) (p k) g
        htloLow hthi (by linarith [hklo]) hkhiLow (hsep target k hne) hcos hg0.le
        (hglt.le.trans (by nlinarith [Real.pi_pos]))
      have hthreshold : Real.pi / 3 < 59 * Real.pi / 150 := by
        nlinarith [Real.pi_pos]
      linarith
  · let g := sharedRelativeArg p anchor k -
      sharedRelativeArg p anchor target
    have hg0 : 0 < g := by dsimp [g]; linarith
    have hglt : g < Real.pi / 3 := by
      dsimp [g]
      have hbound := abs_lt.mp hαlt
      linarith [hbound.1, hneg.2.1]
    have hcos : Real.cos (polarArg (p target) - polarArg (p k)) =
        Real.cos g := by
      rw [hpair]
    by_cases hkh : 2 < ‖p k‖
    · have hangle := shared_AH_angle_gt_60_7 (p target) (p k) g
        htlo hthi hkh.le hkhi (hsep target k hne) hcos hg0.le
        (hglt.le.trans (by nlinarith [Real.pi_pos]))
      have hthreshold : Real.pi / 3 < 607 * Real.pi / 1800 := by
        nlinarith [Real.pi_pos]
      linarith
    · have hkhiLow : ‖p k‖ ≤ 2 := le_of_not_gt hkh
      have htloLow : (699 / 1000 : ℝ) ≤ ‖p target‖ := by
        norm_num at htlo ⊢ <;> linarith
      have hangle := shared_AL_angle_gt_70_8 (p target) (p k) g
        htloLow hthi (by linarith [hklo]) hkhiLow (hsep target k hne) hcos hg0.le
        (hglt.le.trans (by nlinarith [Real.pi_pos]))
      have hthreshold : Real.pi / 3 < 59 * Real.pi / 150 := by
        nlinarith [Real.pi_pos]
      linarith

/-- The two blocker-target contact offsets are charged exactly to their
actual endpoint angular sectors. No gap-charge inequality is assumed. -/
theorem shared_contact_offsets_equal_polar_separations
    (p : Fin 15 → Plane) (y x z : Fin 15) (s : ℝ)
    (hs : 2 < s) (hy : ‖p y‖ = s)
    (hxy : dist (p x) (p y) = 2)
    (hzy : dist (p z) (p y) = 2)
    (hblockx : ‖p x‖ ^ 2 < ⟪p y, p x⟫_ℝ)
    (hblockz : ‖p z‖ ^ 2 < ⟪p y, p z⟫_ℝ)
    (hcross : planeCross (p y) (p x) * planeCross (p y) (p z) < 0) :
    sharedOffset s (sharedContactDelta s (p y) (p x)) +
      sharedOffset s (sharedContactDelta s (p y) (p z)) =
        |sharedRelativeArg p y x| + |sharedRelativeArg p y z| := by
  have hcrossx : planeCross (p y) (p x) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hcross
    norm_num at hcross
  have hcrossz : planeCross (p y) (p z) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcross
    norm_num at hcross
  rw [shared_actual_contact_offset_eq p x y s hs hy hxy hblockx hcrossx,
    shared_actual_contact_offset_eq p z y s hs hy hzy hblockz hcrossz]

/-- Actual shared-blocker geometry supplies the endpoint charge.  The
negative and positive targets are the two non-outer centers; the returned
sector-exclusion facts certify that the corresponding arcs from the blocker
to those targets contain no other touching-inner center.  Thus, in the
six-center cyclic order cut at the blocker, these are the two endpoint gaps.
The charge equality is derived from the contact vectors, not assumed. -/
theorem shared_actual_hcharge
    (p : Fin 15 → Plane) (b s : ℝ) (anchor x z : Fin 15)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK9 : (boundarySet p b).card = 9)
    (hm2 : (nonOuterIndices p b).card = 2)
    (hx : ‖p x‖ < b ∧ ¬TouchesOuter p b x)
    (hz : ‖p z‖ < b ∧ ¬TouchesOuter p b z)
    (hxz : x ≠ z)
    (hanchorT : anchor ∈ touchingInnerSet p b)
    (hy : ‖p anchor‖ = s)
    (hysq : (16 / 3 : ℝ) < s ^ 2)
    (hanchorHi : s ≤ 2385436 / 1000000)
    (hxy : dist (p x) (p anchor) = 2)
    (hzy : dist (p z) (p anchor) = 2)
    (hblockx : ‖p x‖ ^ 2 < ⟪p anchor, p x⟫_ℝ)
    (hblockz : ‖p z‖ ^ 2 < ⟪p anchor, p z⟫_ℝ)
    (hhighCard : ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card = 2)
    (hotherHigh : ∃ w ∈ touchingInnerSet p b,
      w ≠ anchor ∧ 2 < ‖p w‖ ∧ ‖p w‖ < 57 / 25)
    (htouchLow : ∀ k ∈ touchingInnerSet p b,
      (29 / 20 : ℝ) ≤ ‖p k‖)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) :
    ∃ (left right : Fin 15) (g₀ g₅ : ℝ),
      ((left = x ∧ right = z) ∨ (left = z ∧ right = x)) ∧
      sharedRelativeArg p anchor left < 0 ∧
      0 < sharedRelativeArg p anchor right ∧
      g₀ = sharedRelativeArg p anchor right ∧
      g₅ = -sharedRelativeArg p anchor left ∧
      sharedOffset s (sharedContactDelta s (p anchor) (p x)) +
        sharedOffset s (sharedContactDelta s (p anchor) (p z)) ≤ g₀ + g₅ ∧
      (∀ k, ‖p k‖ < b → k ≠ anchor →
        ¬ (sharedRelativeArg p anchor left <
            sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k < 0) ∧
        ¬ (0 < sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k <
            sharedRelativeArg p anchor right)) ∧
      (touchingInnerSet p b).card = 4 := by
  have hysqNorm : (16 / 3 : ℝ) < ‖p anchor‖ ^ 2 := by
    rw [hy]
    exact hysq
  have hs : 2 < s := by
    have hnorm := norm_nonneg (p anchor)
    nlinarith [hysqNorm]
  have hanchorPoint : p anchor ≠ 0 := by
    intro hz0
    rw [hz0] at hysqNorm
    norm_num at hysqNorm
  have hanchorC : planeComplex (p anchor) ≠ 0 := by
    intro hz0
    have hnorm : ‖p anchor‖ = 0 := by
      rw [← planeComplex_norm, hz0]
      simp
    exact hanchorPoint (norm_eq_zero.mp hnorm)
  have hcore := strict_shared_targets_radius_gt_27_div_25
    (p x) (p z) (p anchor) hysqNorm
    (by rw [hy]; exact hanchorHi) hxy hzy hblockx hblockz
    (hpack.2 x z hxz)
  have hFsmall := F_lt_1301_div_1000_of_le_candidateB b hb hbB
  have hxhi : ‖p x‖ ≤ (1301 / 1000 : ℝ) :=
    (hFcap x hx.1 hx.2).trans hFsmall.le
  have hzhi : ‖p z‖ ≤ (1301 / 1000 : ℝ) :=
    (hFcap z hz.1 hz.2).trans hFsmall.le
  have hcross := strict_shared_contacts_cross_negative
    (p x) (p z) (p anchor) (by rw [hy]; nlinarith [hanchorHi])
    hxy hzy hblockx hblockz (hpack.2 x z hxz)
  have hcx : planeCross (p anchor) (p x) ≠ 0 := by
    intro hz0
    rw [hz0, zero_mul] at hcross
    norm_num at hcross
  have hcz : planeCross (p anchor) (p z) ≠ 0 := by
    intro hz0
    rw [hz0, mul_zero] at hcross
    norm_num at hcross
  have hTcard : (touchingInnerSet p b).card = 4 :=
    k9_m2_touching_inner_card_four p b hpack.1 hK9 hm2
  have hxM : x ∈ nonOuterIndices p b := by
    simpa [nonOuterIndices] using hx
  have hzM : z ∈ nonOuterIndices p b := by
    simpa [nonOuterIndices] using hz
  have hMpair : ∀ k, k ∈ nonOuterIndices p b → k = x ∨ k = z := by
    intro k hk
    by_contra hnot
    have hkx : k ≠ x := fun h => hnot (Or.inl h)
    have hkz : k ≠ z := fun h => hnot (Or.inr h)
    have hsub : ({x, z, k} : Finset (Fin 15)) ⊆ nonOuterIndices p b := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact hxM
      · exact hzM
      · exact hk
    have hcard3 : ({x, z, k} : Finset (Fin 15)).card = 3 := by
      simp [hxz, hxz.symm, hkx, hkx.symm, hkz, hkz.symm]
    have hle := Finset.card_le_card hsub
    rw [hcard3] at hle
    omega
  obtain ⟨w, hwT, hwAnchor, hwHigh, hwCap⟩ := hotherHigh
  have hanchorHigh : 2 < ‖p anchor‖ := by
    rw [hy]
    nlinarith [hysq]
  have hTupper (k : Fin 15) (hkT : k ∈ touchingInnerSet p b)
      (hka : k ≠ anchor) : ‖p k‖ ≤ 57 / 25 :=
    shared_other_touching_radius_le_57_div_25 p b anchor w k
      hhighCard hanchorT hwT hkT hanchorHigh hwHigh
      hwAnchor.symm hka hwCap
  have hleftNoOuter (k : Fin 15) (hkT : k ∈ touchingInnerSet p b) :
      k ≠ x ∧ k ≠ z := by
    have hkdata : ‖p k‖ < b ∧ TouchesOuter p b k := by
      simpa [touchingInnerSet] using hkT
    constructor
    · intro heq
      subst k
      exact hx.2 hkdata.2
    · intro heq
      subst k
      exact hz.2 hkdata.2
  have hsectorX := shared_blocker_target_sector_lt_pi_div_three
    p anchor x hysqNorm hxy
  have hsectorZ := shared_blocker_target_sector_lt_pi_div_three
    p anchor z hysqNorm hzy
  by_cases hxpos : 0 < planeCross (p anchor) (p x)
  · have hzneg : planeCross (p anchor) (p z) < 0 := by
      have hcase := (mul_neg_iff.mp hcross).resolve_right
        (fun h => (not_lt_of_ge hxpos.le) h.1)
      exact hcase.2
    have hxarg := shared_relative_arg_positive p anchor x hanchorC hxpos
    have hzarg := shared_relative_arg_negative p anchor z hanchorC hzneg
    have hnoLeft : ∀ k, k ∈ touchingInnerSet p b → k ≠ anchor →
        ¬ (sharedRelativeArg p anchor z < sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k < 0) := by
      intro k hkT hka hbetween
      have hkdata : ‖p k‖ < b ∧ TouchesOuter p b k := by
        simpa [touchingInnerSet] using hkT
      have hne : z ≠ k := by
        intro heq
        subst k
        exact hz.2 hkdata.2
      exact shared_no_touching_center_in_target_sector
        p anchor z k hpack.2 hne hanchorPoint hcore.2.le hzhi
        (htouchLow k hkT) (hTupper k hkT hka) hsectorZ
        (Or.inr ⟨hzarg.2, hbetween.1, hbetween.2⟩)
    have hnoRight : ∀ k, k ∈ touchingInnerSet p b → k ≠ anchor →
        ¬ (0 < sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k < sharedRelativeArg p anchor x) := by
      intro k hkT hka hbetween
      have hkdata : ‖p k‖ < b ∧ TouchesOuter p b k := by
        simpa [touchingInnerSet] using hkT
      have hne : x ≠ k := by
        intro heq
        subst k
        exact hx.2 hkdata.2
      exact shared_no_touching_center_in_target_sector
        p anchor x k hpack.2 hne hanchorPoint hcore.1.le hxhi
        (htouchLow k hkT) (hTupper k hkT hka) hsectorX
        (Or.inl ⟨hxarg.1, hbetween.1, hbetween.2⟩)
    have hnoAll : ∀ k, ‖p k‖ < b → k ≠ anchor →
        ¬ (sharedRelativeArg p anchor z < sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k < 0) ∧
        ¬ (0 < sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k < sharedRelativeArg p anchor x) := by
      intro k hkInner hka
      by_cases hkx : k = x
      · subst k
        constructor <;> intro h <;> linarith [hxarg.1, hxarg.2]
      · by_cases hkz : k = z
        · subst k
          constructor <;> intro h <;> linarith [hxarg.1, hxarg.2,
            hzarg.1, hzarg.2]
        · have hkT : k ∈ touchingInnerSet p b := by
            by_contra hnot
            have hnotOuter : ¬TouchesOuter p b k := by
              intro htouch
              apply hnot
              simpa [touchingInnerSet] using
                (⟨hkInner, htouch⟩ :
                  ‖p k‖ < b ∧ TouchesOuter p b k)
            have hkM : k ∈ nonOuterIndices p b := by
              simpa [nonOuterIndices] using
                (⟨hkInner, hnotOuter⟩ :
                  ‖p k‖ < b ∧ ¬TouchesOuter p b k)
            rcases hMpair k hkM with h | h
            · exact hkx h
            · exact hkz h
          exact ⟨hnoLeft k hkT hka, hnoRight k hkT hka⟩
    have hcharge := shared_contact_offsets_equal_polar_separations
      p anchor x z s hs hy hxy hzy
      hblockx hblockz hcross
    refine ⟨z, x, sharedRelativeArg p anchor x,
      -sharedRelativeArg p anchor z, Or.inr ⟨rfl, rfl⟩,
      hzarg.2, hxarg.1, rfl, rfl, ?_, ?_⟩
    · rw [hcharge, abs_of_pos hxarg.1, abs_of_neg hzarg.2]
    · constructor
      · intro k hkInner hka
        exact hnoAll k hkInner hka
      · exact hTcard
  · have hxneg : planeCross (p anchor) (p x) < 0 := by
      have hne : planeCross (p anchor) (p x) ≠ 0 := hcx
      exact lt_of_le_of_ne (le_of_not_gt hxpos) hne
    have hzpos : 0 < planeCross (p anchor) (p z) := by
      have hcase := (mul_neg_iff.mp hcross).resolve_left
        (fun h => hxpos h.1)
      exact hcase.2
    have hxarg := shared_relative_arg_negative p anchor x hanchorC hxneg
    have hzarg := shared_relative_arg_positive p anchor z hanchorC hzpos
    have hnoLeft : ∀ k, k ∈ touchingInnerSet p b → k ≠ anchor →
        ¬ (sharedRelativeArg p anchor x < sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k < 0) := by
      intro k hkT hka hbetween
      have hkdata : ‖p k‖ < b ∧ TouchesOuter p b k := by
        simpa [touchingInnerSet] using hkT
      have hne : x ≠ k := by
        intro heq
        subst k
        exact hx.2 hkdata.2
      exact shared_no_touching_center_in_target_sector
        p anchor x k hpack.2 hne hanchorPoint hcore.1.le hxhi
        (htouchLow k hkT) (hTupper k hkT hka) hsectorX
        (Or.inr ⟨hxarg.2, hbetween.1, hbetween.2⟩)
    have hnoRight : ∀ k, k ∈ touchingInnerSet p b → k ≠ anchor →
        ¬ (0 < sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k < sharedRelativeArg p anchor z) := by
      intro k hkT hka hbetween
      have hkdata : ‖p k‖ < b ∧ TouchesOuter p b k := by
        simpa [touchingInnerSet] using hkT
      have hne : z ≠ k := by
        intro heq
        subst k
        exact hz.2 hkdata.2
      exact shared_no_touching_center_in_target_sector
        p anchor z k hpack.2 hne hanchorPoint hcore.2.le hzhi
        (htouchLow k hkT) (hTupper k hkT hka) hsectorZ
        (Or.inl ⟨hzarg.1, hbetween.1, hbetween.2⟩)
    have hnoAll : ∀ k, ‖p k‖ < b → k ≠ anchor →
        ¬ (sharedRelativeArg p anchor x < sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k < 0) ∧
        ¬ (0 < sharedRelativeArg p anchor k ∧
          sharedRelativeArg p anchor k < sharedRelativeArg p anchor z) := by
      intro k hkInner hka
      by_cases hkx : k = x
      · subst k
        constructor <;> intro h <;> linarith [hxarg.1, hxarg.2,
          hzarg.1, hzarg.2]
      · by_cases hkz : k = z
        · subst k
          constructor <;> intro h <;> linarith [hzarg.1, hzarg.2]
        · have hkT : k ∈ touchingInnerSet p b := by
            by_contra hnot
            have hnotOuter : ¬TouchesOuter p b k := by
              intro htouch
              apply hnot
              simpa [touchingInnerSet] using
                (⟨hkInner, htouch⟩ :
                  ‖p k‖ < b ∧ TouchesOuter p b k)
            have hkM : k ∈ nonOuterIndices p b := by
              simpa [nonOuterIndices] using
                (⟨hkInner, hnotOuter⟩ :
                  ‖p k‖ < b ∧ ¬TouchesOuter p b k)
            rcases hMpair k hkM with h | h
            · exact hkx h
            · exact hkz h
          exact ⟨hnoLeft k hkT hka, hnoRight k hkT hka⟩
    have hcharge := shared_contact_offsets_equal_polar_separations
      p anchor x z s hs hy hxy hzy
      hblockx hblockz hcross
    refine ⟨x, z, sharedRelativeArg p anchor z,
      -sharedRelativeArg p anchor x, Or.inl ⟨rfl, rfl⟩,
      hxarg.2, hzarg.1, rfl, rfl, ?_, ?_⟩
    · rw [hcharge, abs_of_neg hxarg.2, abs_of_pos hzarg.1]
      nlinarith
    · constructor
      · intro k hkInner hka
        exact hnoAll k hkInner hka
      · exact hTcard

end CP15
