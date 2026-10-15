import CP15.M2K9SharedFirstContact

set_option maxHeartbeats 1000000

open scoped InnerProductSpace

namespace CP15

private noncomputable def sharedRelativeLift
    (p : Fin 15 → Plane) (anchor i : Fin 15) : ℝ :=
  if sharedRelativeArg p anchor i < 0 then
    sharedRelativeArg p anchor i + 2 * Real.pi
  else sharedRelativeArg p anchor i

private theorem shared_relative_pair_cos_local
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

private theorem sharedRelativeLift_pair_cos
    (p : Fin 15 → Plane) (anchor i j : Fin 15)
    (hi : planeComplex (p i) ≠ 0) (hj : planeComplex (p j) ≠ 0)
    (hanchor : planeComplex (p anchor) ≠ 0) :
    Real.cos (polarArg (p i) - polarArg (p j)) =
      Real.cos (sharedRelativeLift p anchor j -
        sharedRelativeLift p anchor i) := by
  have hrel := shared_relative_pair_cos_local p anchor i j hanchor hi hj
  let ai := sharedRelativeArg p anchor i
  let aj := sharedRelativeArg p anchor j
  by_cases hii : ai < 0 <;> by_cases hjj : aj < 0
  · dsimp [sharedRelativeLift, ai, aj]
    rw [if_pos hii, if_pos hjj]
    have hcancel : (aj + 2 * Real.pi) - (ai + 2 * Real.pi) = aj - ai := by ring
    rw [hcancel]
    exact hrel
  · dsimp [sharedRelativeLift, ai, aj]
    rw [if_pos hii, if_neg (not_lt.mpr (le_of_not_gt hjj))]
    have heq : aj - (ai + 2 * Real.pi) = (aj - 2 * Real.pi) - ai := by ring
    rw [heq, cos_sub_two_pi_sub_left]
    exact hrel
  · dsimp [sharedRelativeLift, ai, aj]
    rw [if_neg (not_lt.mpr (le_of_not_gt hii)), if_pos hjj]
    rw [cos_add_two_pi_sub_left]
    exact hrel
  · dsimp [sharedRelativeLift, ai, aj]
    rw [if_neg (not_lt.mpr (le_of_not_gt hii)),
      if_neg (not_lt.mpr (le_of_not_gt hjj))]
    exact hrel

private theorem sharedRelativeLift_eq_iff
    (p : Fin 15 → Plane) (anchor i j : Fin 15)
    (heq : sharedRelativeLift p anchor i =
      sharedRelativeLift p anchor j) :
    sharedRelativeArg p anchor i = sharedRelativeArg p anchor j := by
  let ai := sharedRelativeArg p anchor i
  let aj := sharedRelativeArg p anchor j
  have haiLo : -Real.pi < ai := by
    dsimp [ai, sharedRelativeArg]
    exact Complex.neg_pi_lt_arg _
  have haiHi : ai ≤ Real.pi := by
    dsimp [ai, sharedRelativeArg]
    exact Complex.arg_le_pi _
  have hajLo : -Real.pi < aj := by
    dsimp [aj, sharedRelativeArg]
    exact Complex.neg_pi_lt_arg _
  have hajHi : aj ≤ Real.pi := by
    dsimp [aj, sharedRelativeArg]
    exact Complex.arg_le_pi _
  by_cases hii : ai < 0 <;> by_cases hjj : aj < 0
  · dsimp [sharedRelativeLift, ai, aj] at heq
    rw [if_pos hii, if_pos hjj] at heq
    linarith
  · dsimp [sharedRelativeLift, ai, aj] at heq
    rw [if_pos hii, if_neg (not_lt.mpr (le_of_not_gt hjj))] at heq
    have hπ : 0 < Real.pi := Real.pi_pos
    linarith
  · dsimp [sharedRelativeLift, ai, aj] at heq
    rw [if_neg (not_lt.mpr (le_of_not_gt hii)), if_pos hjj] at heq
    have hπ : 0 < Real.pi := Real.pi_pos
    linarith
  · dsimp [sharedRelativeLift, ai, aj] at heq
    rw [if_neg (not_lt.mpr (le_of_not_gt hii)),
      if_neg (not_lt.mpr (le_of_not_gt hjj))] at heq
    exact heq

private theorem shared_relativeArg_range
    (p : Fin 15 → Plane) (anchor i : Fin 15) :
    -Real.pi < sharedRelativeArg p anchor i ∧
      sharedRelativeArg p anchor i ≤ Real.pi := by
  unfold sharedRelativeArg
  exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩

/-- If two centers in the working radial band have the same direction
from a nonzero anchor, their separation is less than two. Thus actual
separation makes their relative arguments injective on this band. -/
private theorem shared_relativeArg_injective_of_band
    (p : Fin 15 → Plane) (anchor i j : Fin 15)
    (hsep : Separated p 2)
    (hanchor : planeComplex (p anchor) ≠ 0)
    (hi : planeComplex (p i) ≠ 0) (hj : planeComplex (p j) ≠ 0)
    (hilo : (699 / 1000 : ℝ) ≤ ‖p i‖)
    (hihi : ‖p i‖ ≤ 2385436 / 1000000)
    (hjlo : (699 / 1000 : ℝ) ≤ ‖p j‖)
    (hjhi : ‖p j‖ ≤ 2385436 / 1000000)
    (harg : sharedRelativeArg p anchor i =
      sharedRelativeArg p anchor j) : i = j := by
  by_contra hne
  have hd := hsep i j hne
  have hd2 : 4 ≤ dist (p i) (p j) ^ 2 := by
    nlinarith [dist_nonneg (x := p i) (y := p j)]
  have hcos := shared_relative_pair_cos_local p anchor i j
    hanchor hi hj
  rw [harg, sub_self, Real.cos_zero] at hcos
  have hpolar := polar_inner (p i) (p j)
  rw [hcos] at hpolar
  rw [dist_eq_norm, norm_sub_sq_real] at hd2
  have hdiff₁ : ‖p i‖ - ‖p j‖ < 2 := by linarith
  have hdiff₂ : ‖p j‖ - ‖p i‖ < 2 := by linarith
  have hsq : (‖p i‖ - ‖p j‖) ^ 2 < 4 := by
    nlinarith only [hdiff₁, hdiff₂]
  nlinarith only [hd2, hpolar, hsq]

/-- The no-intruder facts returned by `shared_actual_hcharge` put each
other touching center strictly on the complementary arc between the two
targets. Equality with either endpoint or with the anchor is excluded by
same-ray separation. -/
private theorem shared_relative_lift_between
    (p : Fin 15 → Plane) (anchor left right k : Fin 15)
    (hleftgt : -Real.pi < sharedRelativeArg p anchor left)
    (hrightlt : sharedRelativeArg p anchor right < Real.pi)
    (hkargNeAnchor : sharedRelativeArg p anchor k ≠ 0)
    (hkargNeLeft : sharedRelativeArg p anchor k ≠
      sharedRelativeArg p anchor left)
    (hkargNeRight : sharedRelativeArg p anchor k ≠
      sharedRelativeArg p anchor right)
    (hnoLeft : ¬ (sharedRelativeArg p anchor left <
      sharedRelativeArg p anchor k ∧ sharedRelativeArg p anchor k < 0))
    (hnoRight : ¬ (0 < sharedRelativeArg p anchor k ∧
      sharedRelativeArg p anchor k < sharedRelativeArg p anchor right)) :
    sharedRelativeArg p anchor right < sharedRelativeLift p anchor k ∧
      sharedRelativeLift p anchor k <
        sharedRelativeArg p anchor left + 2 * Real.pi := by
  have hkRange := shared_relativeArg_range p anchor k
  by_cases hkneg : sharedRelativeArg p anchor k < 0
  · have hkleft : sharedRelativeArg p anchor k <
        sharedRelativeArg p anchor left := by
      have hnot : ¬ sharedRelativeArg p anchor left <
          sharedRelativeArg p anchor k := by
        intro hlt
        exact hnoLeft ⟨hlt, hkneg⟩
      have hle := le_of_not_gt hnot
      by_contra hnotlt
      exact hkargNeLeft (le_antisymm hle (le_of_not_gt hnotlt))
    constructor
    · have hπ : Real.pi < sharedRelativeArg p anchor k +
          2 * Real.pi := by linarith [hkRange.1, Real.pi_pos]
      simpa [sharedRelativeLift, hkneg] using hrightlt.trans hπ
    · simp [sharedRelativeLift, hkneg]
      exact hkleft
  · have hkpos : 0 < sharedRelativeArg p anchor k :=
      lt_of_le_of_ne (le_of_not_gt hkneg) (Ne.symm hkargNeAnchor)
    have hrightk : sharedRelativeArg p anchor right <
        sharedRelativeArg p anchor k := by
      have hnot : ¬ sharedRelativeArg p anchor k <
          sharedRelativeArg p anchor right := by
        intro hlt
        exact hnoRight ⟨hkpos, hlt⟩
      have hle := le_of_not_gt hnot
      by_contra hnotlt
      have heq : sharedRelativeArg p anchor k =
          sharedRelativeArg p anchor right :=
        le_antisymm (le_of_not_gt hnotlt) hle
      exact hkargNeRight heq
    constructor
    · simp [sharedRelativeLift, hkneg]
      exact hrightk
    · have hπ : sharedRelativeArg p anchor k <
          sharedRelativeArg p anchor left + 2 * Real.pi := by
        linarith [hkRange.2, hleftgt, Real.pi_pos]
      simpa [sharedRelativeLift, hkneg] using hπ

private theorem plane_inner_basis_identity (y u v : Plane) :
    ‖y‖ ^ 2 * ⟪u, v⟫_ℝ =
      ⟪y, u⟫_ℝ * ⟪y, v⟫_ℝ +
        planeCross y u * planeCross y v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [planeCross, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The actual two contact vectors at a shared blocker subtend at least
`pi/3`. This follows directly from their distance and their opposite
cross-product signs; no angular gap charge is used. -/
theorem shared_contact_angle_spread
    (x z y : Plane) (s : ℝ)
    (hs : 2 < s) (hy : ‖y‖ = s)
    (hxy : dist x y = 2) (hzy : dist z y = 2)
    (hblockx : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ)
    (hblockz : ‖z‖ ^ 2 < ⟪y, z⟫_ℝ)
    (hcross : planeCross y x * planeCross y z < 0)
    (hxz : 2 ≤ dist x z) :
    Real.pi / 3 ≤ sharedContactDelta s y x +
      sharedContactDelta s y z := by
  have hcx : planeCross y x ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hcross
    norm_num at hcross
  have hcz : planeCross y z ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hcross
    norm_num at hcross
  have hdx := shared_contact_delta_domain x y s hs hy hxy hblockx hcx
  have hdz := shared_contact_delta_domain z y s hs hy hzy hblockz hcz
  let δx := sharedContactDelta s y x
  let δz := sharedContactDelta s y z
  let u := x - y
  let v := z - y
  have hu : ‖u‖ = 2 := by
    dsimp [u]
    rw [← dist_eq_norm]
    exact hxy
  have hv : ‖v‖ = 2 := by
    dsimp [v]
    rw [← dist_eq_norm]
    simpa [dist_comm] using hzy
  have hdotu : ⟪y, u⟫_ℝ = -2 * s * Real.cos δx := by
    dsimp [u, δx]
    linarith [hdx.2.2]
  have hdotv : ⟪y, v⟫_ℝ = -2 * s * Real.cos δz := by
    dsimp [v, δz]
    linarith [hdz.2.2]
  have hcrossu : planeCross y u = planeCross y x := by
    dsimp [u]
    simp [planeCross, PiLp.sub_apply]
    ring
  have hcrossv : planeCross y v = planeCross y z := by
    dsimp [v]
    simp [planeCross, PiLp.sub_apply]
    ring
  have hgramu := plane_dot_cross_identity y u u
  rw [real_inner_self_eq_norm_sq, hu, hy] at hgramu
  rw [hdotu] at hgramu
  have hcrossuSq : planeCross y u ^ 2 =
      (2 * s * Real.sin δx) ^ 2 := by
    have hsin := Real.sin_sq_add_cos_sq δx
    nlinarith [hgramu, hsin]
  have hgramv := plane_dot_cross_identity y v v
  rw [real_inner_self_eq_norm_sq, hv, hy] at hgramv
  rw [hdotv] at hgramv
  have hcrossvSq : planeCross y v ^ 2 =
      (2 * s * Real.sin δz) ^ 2 := by
    have hsin := Real.sin_sq_add_cos_sq δz
    nlinarith [hgramv, hsin]
  have hsx : 0 < Real.sin δx :=
    Real.sin_pos_of_pos_of_lt_pi hdx.1
      (hdx.2.1.trans (by
        have harc := Real.arccos_lt_pi_div_two.mpr (by positivity :
          (0 : ℝ) < 2 / s)
        linarith [Real.pi_pos]))
  have hsz : 0 < Real.sin δz :=
    Real.sin_pos_of_pos_of_lt_pi hdz.1
      (hdz.2.1.trans (by
        have harc := Real.arccos_lt_pi_div_two.mpr (by positivity :
          (0 : ℝ) < 2 / s)
        linarith [Real.pi_pos]))
  have hcrossuAbs : |planeCross y u| = 2 * s * Real.sin δx := by
    have hsq : |planeCross y u| ^ 2 =
        (2 * s * Real.sin δx) ^ 2 := by simpa [sq_abs] using hcrossuSq
    have hr : 0 ≤ 2 * s * Real.sin δx := by positivity
    nlinarith [abs_nonneg (planeCross y u)]
  have hcrossvAbs : |planeCross y v| = 2 * s * Real.sin δz := by
    have hsq : |planeCross y v| ^ 2 =
        (2 * s * Real.sin δz) ^ 2 := by simpa [sq_abs] using hcrossvSq
    have hr : 0 ≤ 2 * s * Real.sin δz := by positivity
    nlinarith [abs_nonneg (planeCross y v)]
  have hcrossuvneg : planeCross y u * planeCross y v < 0 := by
    rw [hcrossu, hcrossv]
    exact hcross
  have hcrossuv : planeCross y u * planeCross y v =
      -(4 * s ^ 2 * Real.sin δx * Real.sin δz) := by
    have habs : |planeCross y u * planeCross y v| =
        -(planeCross y u * planeCross y v) := abs_of_neg hcrossuvneg
    rw [abs_mul, hcrossuAbs, hcrossvAbs] at habs
    nlinarith only [habs]
  have hbasis := plane_inner_basis_identity y u v
  have hinner : ⟪u, v⟫_ℝ = 4 * Real.cos (δx + δz) := by
    rw [hy, hdotu, hdotv, hcrossuv] at hbasis
    have hcos := Real.cos_add δx δz
    have hprod : s ^ 2 * ⟪u, v⟫_ℝ =
        4 * s ^ 2 *
          (Real.cos δx * Real.cos δz -
            Real.sin δx * Real.sin δz) := by
      nlinarith [hbasis]
    rw [hcos]
    have hs2 : 0 < s ^ 2 := by positivity
    nlinarith [hprod]
  have hxdiff : x - z = u - v := by
    dsimp [u, v]
    abel
  have hdist2 : 4 ≤ ‖x - z‖ ^ 2 := by
    rw [← dist_eq_norm]
    nlinarith [hxz, dist_nonneg (x := x) (y := z)]
  rw [hxdiff, norm_sub_sq_real, hu, hv, hinner] at hdist2
  have hcosle : Real.cos (δx + δz) ≤ 1 / 2 := by
    nlinarith only [hdist2]
  have hsum0 : 0 < δx + δz := by
    dsimp [δx, δz]
    linarith [hdx.1, hdz.1]
  have hsumPi : δx + δz < Real.pi := by
    have harc := Real.arccos_lt_pi_div_two.mpr (by positivity :
      (0 : ℝ) < 2 / s)
    have hdxPi : δx < Real.pi / 2 := hdx.2.1.trans harc
    have hdzPi : δz < Real.pi / 2 := hdz.2.1.trans harc
    linarith
  by_contra hnot
  have hsumlt : δx + δz < Real.pi / 3 := lt_of_not_ge hnot
  have hpi : Real.pi / 3 ≤ Real.pi := by linarith [Real.pi_pos]
  have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi hsum0.le hpi hsumlt
  rw [Real.cos_pi_div_three] at hcoslt
  linarith

private theorem planeComplex_ne_zero_of_norm_pos
    (x : Plane) (hx : 0 < ‖x‖) : planeComplex x ≠ 0 := by
  intro hz
  have hn : ‖x‖ = 0 := by
    rw [← planeComplex_norm, hz]
    simp
  linarith

private theorem shared_AH60_gap_bound
    (x y : Plane) (g : ℝ)
    (hxlo : (27 / 25 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (2 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ 57 / 25)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) : 607 * Real.pi / 1800 < g := by
  by_cases hgpi : g ≤ Real.pi
  · exact shared_AH_angle_gt_60_7 x y g hxlo hxhi hylo hyhi
      hsep hcos hg0 hgpi
  · have hlarge : Real.pi < g := lt_of_not_ge hgpi
    have hthreshold : 607 * Real.pi / 1800 < Real.pi := by
      nlinarith [Real.pi_pos]
    exact hthreshold.trans hlarge

private theorem shared_AL_gap_bound
    (x y : Plane) (g : ℝ)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖)
    (hxhi : ‖x‖ ≤ 1301 / 1000)
    (hylo : (29 / 20 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ 2)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) : 59 * Real.pi / 150 < g := by
  by_cases hgpi : g ≤ Real.pi
  · exact shared_AL_angle_gt_70_8 x y g hxlo hxhi (by linarith [hylo]) hyhi
      hsep hcos hg0 hgpi
  · have hlarge : Real.pi < g := lt_of_not_ge hgpi
    have hthreshold : 59 * Real.pi / 150 < Real.pi := by
      nlinarith [Real.pi_pos]
    exact hthreshold.trans hlarge

private theorem shared_HL_gap_bound
    (x y : Plane) (g : ℝ)
    (hxlo : (2 : ℝ) ≤ ‖x‖) (hxhi : ‖x‖ ≤ 57 / 25)
    (hylo : (29 / 20 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ 2)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) : 23 * Real.pi / 75 < g := by
  by_cases hgpi : g ≤ Real.pi
  · exact shared_HL_angle_gt_55_2 x y g hxlo hxhi hylo hyhi
      hsep hcos hg0 hgpi
  · have hlarge : Real.pi < g := lt_of_not_ge hgpi
    have hthreshold : 23 * Real.pi / 75 < Real.pi := by
      nlinarith [Real.pi_pos]
    exact hthreshold.trans hlarge

private theorem shared_LL_gap_bound
    (x y : Plane) (g : ℝ)
    (hxlo : (29 / 20 : ℝ) ≤ ‖x‖) (hxhi : ‖x‖ ≤ 2)
    (hylo : (29 / 20 : ℝ) ≤ ‖y‖) (hyhi : ‖y‖ ≤ 2)
    (hsep : 2 ≤ dist x y)
    (hcos : Real.cos (polarArg x - polarArg y) = Real.cos g)
    (hg0 : 0 ≤ g) : Real.pi / 3 ≤ g := by
  by_cases hgpi : g ≤ Real.pi
  · exact shared_LL_angle_ge_60 x y g (by linarith [hxlo]) hxhi
      (by linarith [hylo]) hyhi
      hsep hcos hg0 hgpi
  · have hlarge : Real.pi < g := lt_of_not_ge hgpi
    linarith

/-- The actual three touching centers other than the common blocker sort
strictly between the two non-outer targets on the complementary angular
arc. Their radius classes occur in exactly one of the three displayed
orders, which supplies the four middle-gap bounds. -/
theorem shared_actual_middle_gap_data
    (p : Fin 15 → Plane) (b : ℝ)
    (anchor left right : Fin 15) (g₀ g₅ : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hanchorT : anchor ∈ touchingInnerSet p b)
    (hanchorHigh : 2 < ‖p anchor‖)
    (hanchorHi : ‖p anchor‖ ≤ 2385436 / 1000000)
    (hleftNoOuter : ¬TouchesOuter p b left)
    (hrightNoOuter : ¬TouchesOuter p b right)
    (hleftLo : (27 / 25 : ℝ) ≤ ‖p left‖)
    (hleftHi : ‖p left‖ ≤ 1301 / 1000)
    (hrightLo : (27 / 25 : ℝ) ≤ ‖p right‖)
    (hrightHi : ‖p right‖ ≤ 1301 / 1000)
    (hleftNeg : sharedRelativeArg p anchor left < 0)
    (hrightPos : 0 < sharedRelativeArg p anchor right)
    (hleftSector : |sharedRelativeArg p anchor left| < Real.pi / 3)
    (hrightSector : |sharedRelativeArg p anchor right| < Real.pi / 3)
    (hg₀ : g₀ = sharedRelativeArg p anchor right)
    (hg₅ : g₅ = -sharedRelativeArg p anchor left)
    (hno : ∀ k, ‖p k‖ < b → k ≠ anchor →
      ¬ (sharedRelativeArg p anchor left <
          sharedRelativeArg p anchor k ∧
        sharedRelativeArg p anchor k < 0) ∧
      ¬ (0 < sharedRelativeArg p anchor k ∧
        sharedRelativeArg p anchor k < sharedRelativeArg p anchor right))
    (hTcard : (touchingInnerSet p b).card = 4)
    (hhighCard : ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card = 2)
    (hotherHigh : ∃ w ∈ touchingInnerSet p b,
      w ≠ anchor ∧ 2 < ‖p w‖ ∧ ‖p w‖ < 57 / 25)
    (htouchLow : ∀ k, k ∈ touchingInnerSet p b →
      (29 / 20 : ℝ) ≤ ‖p k‖) :
    ∃ g₁ g₂ g₃ g₄ : ℝ,
      g₀ + g₁ + g₂ + g₃ + g₄ + g₅ = 2 * Real.pi ∧
      (((59 * Real.pi / 150 < g₁) ∧
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
          (607 * Real.pi / 1800 < g₄))) := by
  classical
  let T := touchingInnerSet p b
  let O := T.erase anchor
  have hOcard : O.card = 3 := by
    have h := Finset.card_erase_of_mem hanchorT
    dsimp [T, O] at h ⊢
    rw [hTcard] at h
    norm_num at h ⊢
    exact h
  obtain ⟨w, hwT, hwAnchor, hwHigh, hwCap⟩ := hotherHigh
  have hanchorT' : anchor ∈ T := by simpa [T] using hanchorT
  have hwT' : w ∈ T := by simpa [T] using hwT
  have hwO : w ∈ O := Finset.mem_erase.mpr ⟨hwAnchor, hwT'⟩
  have hupperT : ∀ k, k ∈ T → k ≠ anchor → ‖p k‖ ≤ 57 / 25 := by
    intro k hkT hka
    exact shared_other_touching_radius_le_57_div_25 p b anchor w k
      hhighCard hanchorT' hwT' hkT hanchorHigh hwHigh
      hwAnchor.symm hka hwCap
  have hanchorC : planeComplex (p anchor) ≠ 0 :=
    planeComplex_ne_zero_of_norm_pos (p anchor) (by linarith)
  have hleftC : planeComplex (p left) ≠ 0 :=
    planeComplex_ne_zero_of_norm_pos (p left) (by linarith [hleftLo])
  have hrightC : planeComplex (p right) ≠ 0 :=
    planeComplex_ne_zero_of_norm_pos (p right) (by linarith [hrightLo])
  have hleftBroadLo : (699 / 1000 : ℝ) ≤ ‖p left‖ := by
    linarith [hleftLo]
  have hrightBroadLo : (699 / 1000 : ℝ) ≤ ‖p right‖ := by
    linarith [hrightLo]
  have hleftBroadHi : ‖p left‖ ≤ 2385436 / 1000000 := by
    linarith [hleftHi]
  have hrightBroadHi : ‖p right‖ ≤ 2385436 / 1000000 := by
    linarith [hrightHi]
  have hanchorBroadLo : (699 / 1000 : ℝ) ≤ ‖p anchor‖ := by
    linarith
  have hsourceBroadLo : ∀ k, k ∈ O →
      (699 / 1000 : ℝ) ≤ ‖p k‖ := by
    intro k hkO
    have hkT : k ∈ T := (Finset.mem_erase.mp hkO).2
    have hklo := htouchLow k hkT
    linarith
  have hsourceBroadHi : ∀ k, k ∈ O →
      ‖p k‖ ≤ 2385436 / 1000000 := by
    intro k hkO
    have hkErase := Finset.mem_erase.mp hkO
    have hhi := hupperT k hkErase.2 hkErase.1
    linarith
  have hsourceC : ∀ k, k ∈ O → planeComplex (p k) ≠ 0 := by
    intro k hkO
    apply planeComplex_ne_zero_of_norm_pos
    have hlo := hsourceBroadLo k hkO
    linarith
  have hargInjective : ∀ i j, i = anchor ∨ i = left ∨ i = right ∨ i ∈ O →
      j = anchor ∨ j = left ∨ j = right ∨ j ∈ O →
      sharedRelativeArg p anchor i = sharedRelativeArg p anchor j → i = j := by
    intro i j hi hj harg
    have hiC : planeComplex (p i) ≠ 0 := by
      rcases hi with rfl | rfl | rfl | h
      · exact hanchorC
      · exact hleftC
      · exact hrightC
      · exact hsourceC i h
    have hjC : planeComplex (p j) ≠ 0 := by
      rcases hj with rfl | rfl | rfl | h
      · exact hanchorC
      · exact hleftC
      · exact hrightC
      · exact hsourceC j h
    have hilo : (699 / 1000 : ℝ) ≤ ‖p i‖ := by
      rcases hi with rfl | rfl | rfl | h
      · exact hanchorBroadLo
      · exact hleftBroadLo
      · exact hrightBroadLo
      · exact hsourceBroadLo i h
    have hihi : ‖p i‖ ≤ 2385436 / 1000000 := by
      rcases hi with rfl | rfl | rfl | h
      · exact hanchorHi
      · exact hleftBroadHi
      · exact hrightBroadHi
      · exact hsourceBroadHi i h
    have hjlo : (699 / 1000 : ℝ) ≤ ‖p j‖ := by
      rcases hj with rfl | rfl | rfl | h
      · exact hanchorBroadLo
      · exact hleftBroadLo
      · exact hrightBroadLo
      · exact hsourceBroadLo j h
    have hjhi : ‖p j‖ ≤ 2385436 / 1000000 := by
      rcases hj with rfl | rfl | rfl | h
      · exact hanchorHi
      · exact hleftBroadHi
      · exact hrightBroadHi
      · exact hsourceBroadHi j h
    exact shared_relativeArg_injective_of_band p anchor i j hpack.2
      hanchorC hiC hjC hilo hihi hjlo hjhi harg
  have hrightLtPi : sharedRelativeArg p anchor right < Real.pi := by
    have h := abs_lt.mp hrightSector
    linarith
  have hleftGtNegPi : -Real.pi < sharedRelativeArg p anchor left :=
    (shared_relativeArg_range p anchor left).1
  have hthetaRight : sharedRelativeLift p anchor right =
      sharedRelativeArg p anchor right := by
    simp [sharedRelativeLift, not_lt.mpr hrightPos.le]
  have hthetaLeft : sharedRelativeLift p anchor left =
      sharedRelativeArg p anchor left + 2 * Real.pi := by
    simp [sharedRelativeLift, hleftNeg]
  let angles : Finset ℝ := O.image (fun k => sharedRelativeLift p anchor k)
  have hliftInj : ∀ i j, i ∈ O → j ∈ O →
      sharedRelativeLift p anchor i = sharedRelativeLift p anchor j → i = j := by
    intro i j hi hj heq
    have harg := sharedRelativeLift_eq_iff p anchor i j heq
    exact hargInjective i j (Or.inr (Or.inr (Or.inr hi)))
      (Or.inr (Or.inr (Or.inr hj))) harg
  have hanglesCard : angles.card = 3 := by
    dsimp [angles]
    calc
      (O.image (fun k => sharedRelativeLift p anchor k)).card = O.card :=
        (Finset.card_image_iff).2 (by
          intro i hi j hj heq
          exact hliftInj i j hi hj heq)
      _ = 3 := hOcard
  let order : Fin 3 ↪o ℝ := angles.orderEmbOfFin hanglesCard
  let θ : Fin 3 → ℝ := fun i => order i
  have hmono : StrictMono θ := order.strictMono
  have hmemAngle (i : Fin 3) : θ i ∈ angles :=
    Finset.orderEmbOfFin_mem angles hanglesCard i
  let src (i : Fin 3) : Fin 15 :=
    Classical.choose (Finset.mem_image.mp (hmemAngle i))
  have hsrcSpec (i : Fin 3) :
      src i ∈ O ∧ sharedRelativeLift p anchor (src i) = θ i :=
    Classical.choose_spec (Finset.mem_image.mp (hmemAngle i))
  have hsrcInj : Function.Injective src := by
    intro i j hij
    apply hmono.injective
    calc
      θ i = sharedRelativeLift p anchor (src i) := (hsrcSpec i).2.symm
      _ = sharedRelativeLift p anchor (src j) := by rw [hij]
      _ = θ j := (hsrcSpec j).2
  have hnotLeftT : left ∉ T := by
    intro h
    have hdata : ‖p left‖ < b ∧ TouchesOuter p b left := by
      simpa [T, touchingInnerSet] using h
    exact hleftNoOuter hdata.2
  have hnotRightT : right ∉ T := by
    intro h
    have hdata : ‖p right‖ < b ∧ TouchesOuter p b right := by
      simpa [T, touchingInnerSet] using h
    exact hrightNoOuter hdata.2
  have hbetween (i : Fin 3) :
      sharedRelativeArg p anchor right <
          sharedRelativeLift p anchor (src i) ∧
        sharedRelativeLift p anchor (src i) <
          sharedRelativeArg p anchor left + 2 * Real.pi := by
    have hsi := hsrcSpec i
    have hkErase := Finset.mem_erase.mp hsi.1
    have hkTdata : ‖p (src i)‖ < b ∧
        TouchesOuter p b (src i) := by
      simpa [T, touchingInnerSet] using hkErase.2
    have hNo := hno (src i) hkTdata.1 hkErase.1
    have hargNeAnchor : sharedRelativeArg p anchor (src i) ≠ 0 := by
      intro heq
      have hself : sharedRelativeArg p anchor anchor = 0 := by
        unfold sharedRelativeArg
        exact Complex.arg_div_self _
      have heq' : sharedRelativeArg p anchor (src i) =
          sharedRelativeArg p anchor anchor := by simpa [hself] using heq
      have hidx := hargInjective (src i) anchor
        (Or.inr (Or.inr (Or.inr hsi.1))) (Or.inl rfl) heq'
      exact hkErase.1 hidx
    have hargNeLeft : sharedRelativeArg p anchor (src i) ≠
        sharedRelativeArg p anchor left := by
      intro heq
      have hidx := hargInjective (src i) left
        (Or.inr (Or.inr (Or.inr hsi.1))) (Or.inr (Or.inl rfl)) heq
      exact hnotLeftT (hidx ▸ hkErase.2)
    have hargNeRight : sharedRelativeArg p anchor (src i) ≠
        sharedRelativeArg p anchor right := by
      intro heq
      have hidx := hargInjective (src i) right
        (Or.inr (Or.inr (Or.inr hsi.1))) (Or.inr (Or.inr (Or.inl rfl))) heq
      exact hnotRightT (hidx ▸ hkErase.2)
    have hb := shared_relative_lift_between p anchor left right (src i)
      hleftGtNegPi hrightLtPi hargNeAnchor
      hargNeLeft hargNeRight hNo.1 hNo.2
    constructor
    · rw [← hthetaRight]
      simpa [hthetaRight] using hb.1
    · rw [← hthetaLeft]
      simpa [hthetaLeft] using hb.2
  have hthetaBetween (i : Fin 3) :
      sharedRelativeLift p anchor right < θ i ∧
        θ i < sharedRelativeLift p anchor left := by
    have h := hbetween i
    rw [(hsrcSpec i).2] at h
    constructor
    · simpa [hthetaRight] using h.1
    · simpa [hthetaLeft] using h.2
  let sourceSet : Finset (Fin 15) := Finset.univ.image src
  have hsourceSetSubset : sourceSet ⊆ O := by
    intro k hk
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hk
    rw [← hi]
    exact (hsrcSpec i).1
  have hsourceSetCard : sourceSet.card = 3 := by
    dsimp [sourceSet]
    rw [Finset.card_image_of_injective Finset.univ hsrcInj]
    simp
  have hOle : O.card ≤ sourceSet.card := by rw [hOcard, hsourceSetCard]
  have hsourceSetEq : sourceSet = O :=
    Finset.eq_of_subset_of_card_le hsourceSetSubset hOle
  have hwSource : w ∈ sourceSet := by
    rw [hsourceSetEq]
    exact hwO
  obtain ⟨c, -, hcw⟩ := Finset.mem_image.mp hwSource
  have hnotHighOther (i : Fin 3) (hi : src i ∈ O)
      (hiw : src i ≠ w) : ‖p (src i)‖ ≤ 2 := by
    by_contra hnot
    have hhigh : 2 < ‖p (src i)‖ := lt_of_not_ge hnot
    have hsiErase := Finset.mem_erase.mp hi
    have hsiT : src i ∈ T := hsiErase.2
    have hsubset : ({anchor, w, src i} : Finset (Fin 15)) ⊆
        T.filter (fun k => 2 < ‖p k‖) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · simp only [Finset.mem_filter]
        exact ⟨hanchorT', hanchorHigh⟩
      · simp only [Finset.mem_filter]
        exact ⟨hwT', hwHigh⟩
      · simp only [Finset.mem_filter]
        exact ⟨hsiT, hhigh⟩
    have htriple : ({anchor, w, src i} : Finset (Fin 15)).card = 3 := by
      have hne₁ : anchor ∉ ({w, src i} : Finset (Fin 15)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hwAnchor.symm, hsiErase.1.symm⟩
      have hne₂ : w ∉ ({src i} : Finset (Fin 15)) := by
        simpa using hiw.symm
      rw [Finset.card_insert_of_notMem hne₁,
        Finset.card_insert_of_notMem hne₂]
      simp
    have hle := Finset.card_le_card hsubset
    rw [htriple, hhighCard] at hle
    omega
  have hsrcBroadUpper (i : Fin 3) : ‖p (src i)‖ ≤ 57 / 25 :=
    hupperT (src i) ((Finset.mem_erase.mp (hsrcSpec i).1).2)
      ((Finset.mem_erase.mp (hsrcSpec i).1).1)
  let g₁ : ℝ := θ 0 - sharedRelativeArg p anchor right
  let g₂ : ℝ := θ 1 - θ 0
  let g₃ : ℝ := θ 2 - θ 1
  let g₄ : ℝ := sharedRelativeArg p anchor left +
    2 * Real.pi - θ 2
  have hsum : g₀ + g₁ + g₂ + g₃ + g₄ + g₅ = 2 * Real.pi := by
    rw [hg₀, hg₅]
    dsimp [g₁, g₂, g₃, g₄]
    ring
  have hg₁ : 0 < g₁ := by
    dsimp [g₁]
    linarith [(hthetaBetween (0 : Fin 3)).1]
  have hg₂ : 0 < g₂ := by
    dsimp [g₂]
    linarith [hmono (by decide : (0 : Fin 3) < (1 : Fin 3))]
  have hg₃ : 0 < g₃ := by
    dsimp [g₃]
    linarith [hmono (by decide : (1 : Fin 3) < (2 : Fin 3))]
  have hg₄ : 0 < g₄ := by
    dsimp [g₄]
    have h := (hthetaBetween 2).2
    linarith [hthetaLeft]
  have hcos₁ : Real.cos (polarArg (p right) -
      polarArg (p (src 0))) = Real.cos g₁ := by
    have h := sharedRelativeLift_pair_cos p anchor right (src 0)
      hrightC (hsourceC (src 0) (hsrcSpec 0).1) hanchorC
    rw [(hsrcSpec 0).2, hthetaRight] at h
    simpa [g₁] using h
  have hcos₂ : Real.cos (polarArg (p (src 0)) -
      polarArg (p (src 1))) = Real.cos g₂ := by
    have h := sharedRelativeLift_pair_cos p anchor (src 0) (src 1)
      (hsourceC (src 0) (hsrcSpec 0).1)
      (hsourceC (src 1) (hsrcSpec 1).1) hanchorC
    rw [(hsrcSpec 0).2, (hsrcSpec 1).2] at h
    simpa [g₂] using h
  have hcos₃ : Real.cos (polarArg (p (src 1)) -
      polarArg (p (src 2))) = Real.cos g₃ := by
    have h := sharedRelativeLift_pair_cos p anchor (src 1) (src 2)
      (hsourceC (src 1) (hsrcSpec 1).1)
      (hsourceC (src 2) (hsrcSpec 2).1) hanchorC
    rw [(hsrcSpec 1).2, (hsrcSpec 2).2] at h
    simpa [g₃] using h
  have hcos₄ : Real.cos (polarArg (p left) -
      polarArg (p (src 2))) = Real.cos g₄ := by
    have h := sharedRelativeLift_pair_cos p anchor left (src 2)
      hleftC (hsourceC (src 2) (hsrcSpec 2).1) hanchorC
    rw [(hsrcSpec 2).2, hthetaLeft] at h
    have hneg : θ 2 - (sharedRelativeArg p anchor left +
        2 * Real.pi) = -g₄ := by dsimp [g₄]; ring
    rw [hneg, Real.cos_neg] at h
    exact h
  have hrightNe0 : right ≠ src 0 := by
    intro heq
    exact hnotRightT (heq ▸ (Finset.mem_erase.mp (hsrcSpec 0).1).2)
  have h01Ne : src 0 ≠ src 1 := hsrcInj.ne (by decide)
  have h12Ne : src 1 ≠ src 2 := hsrcInj.ne (by decide)
  have h2leftNe : src 2 ≠ left := by
    intro heq
    exact hnotLeftT (heq ▸ (Finset.mem_erase.mp (hsrcSpec 2).1).2)
  have hsepRight0 : 2 ≤ dist (p right) (p (src 0)) :=
    hpack.2 right (src 0) hrightNe0
  have hsep01 : 2 ≤ dist (p (src 0)) (p (src 1)) :=
    hpack.2 (src 0) (src 1) h01Ne
  have hsep12 : 2 ≤ dist (p (src 1)) (p (src 2)) :=
    hpack.2 (src 1) (src 2) h12Ne
  have hsep2Left : 2 ≤ dist (p left) (p (src 2)) := by
    have h := hpack.2 (src 2) left h2leftNe
    simpa [dist_comm] using h
  have hrightInnerLo : (699 / 1000 : ℝ) ≤ ‖p right‖ := by
    linarith [hrightLo]
  have hleftInnerLo : (699 / 1000 : ℝ) ≤ ‖p left‖ := by
    linarith [hleftLo]
  have hlow0 : (29 / 20 : ℝ) ≤ ‖p (src 0)‖ :=
    htouchLow (src 0) ((Finset.mem_erase.mp (hsrcSpec 0).1).2)
  have hlow1 : (29 / 20 : ℝ) ≤ ‖p (src 1)‖ :=
    htouchLow (src 1) ((Finset.mem_erase.mp (hsrcSpec 1).1).2)
  have hlow2 : (29 / 20 : ℝ) ≤ ‖p (src 2)‖ :=
    htouchLow (src 2) ((Finset.mem_erase.mp (hsrcSpec 2).1).2)
  have hupper0 : ‖p (src 0)‖ ≤ 57 / 25 := hsrcBroadUpper 0
  have hupper1 : ‖p (src 1)‖ ≤ 57 / 25 := hsrcBroadUpper 1
  have hupper2 : ‖p (src 2)‖ ≤ 57 / 25 := hsrcBroadUpper 2
  fin_cases c
  · have hw0 : src (0 : Fin 3) = w := by simpa using hcw
    have hq0high : 2 < ‖p (src 0)‖ := by rw [hw0]; exact hwHigh
    have hq1low : ‖p (src 1)‖ ≤ 2 := by
      apply hnotHighOther (1 : Fin 3) (hsrcSpec 1).1
      intro heq
      have hidx : (0 : Fin 3) = 1 := hsrcInj (hw0.trans heq.symm)
      exact (by decide : (0 : Fin 3) ≠ 1) hidx
    have hq2low : ‖p (src 2)‖ ≤ 2 := by
      apply hnotHighOther (2 : Fin 3) (hsrcSpec 2).1
      intro heq
      have hidx : (0 : Fin 3) = 2 := hsrcInj (hw0.trans heq.symm)
      exact (by decide : (0 : Fin 3) ≠ 2) hidx
    have h₁ := shared_AH60_gap_bound (p right) (p (src 0)) g₁
      hrightLo hrightHi (by linarith [hq0high]) hupper0
      hsepRight0 hcos₁ hg₁.le
    have h₂ := shared_HL_gap_bound (p (src 0)) (p (src 1)) g₂
      (by linarith [hq0high]) hupper0 hlow1 hq1low
      hsep01 hcos₂ hg₂.le
    have h₃ := shared_LL_gap_bound (p (src 1)) (p (src 2)) g₃
      hlow1 hq1low hlow2 hq2low hsep12 hcos₃ hg₃.le
    have h₄ := shared_AL_gap_bound (p left) (p (src 2)) g₄
      hleftInnerLo hleftHi hlow2 hq2low hsep2Left hcos₄ hg₄.le
    refine ⟨g₁, g₂, g₃, g₄, hsum, Or.inr (Or.inl ?_)⟩
    exact ⟨h₁, h₂, h₃, h₄⟩
  · have hw1 : src (1 : Fin 3) = w := by simpa using hcw
    have hq1high : 2 < ‖p (src 1)‖ := by rw [hw1]; exact hwHigh
    have hq0low : ‖p (src 0)‖ ≤ 2 := by
      apply hnotHighOther (0 : Fin 3) (hsrcSpec 0).1
      intro heq
      have hidx : (1 : Fin 3) = 0 := hsrcInj (hw1.trans heq.symm)
      exact (by decide : (1 : Fin 3) ≠ 0) hidx
    have hq2low : ‖p (src 2)‖ ≤ 2 := by
      apply hnotHighOther (2 : Fin 3) (hsrcSpec 2).1
      intro heq
      have hidx : (1 : Fin 3) = 2 := hsrcInj (hw1.trans heq.symm)
      exact (by decide : (1 : Fin 3) ≠ 2) hidx
    have hcos₂rev : Real.cos (polarArg (p (src 1)) -
        polarArg (p (src 0))) = Real.cos g₂ := by
      rw [show polarArg (p (src 1)) - polarArg (p (src 0)) =
        -(polarArg (p (src 0)) - polarArg (p (src 1))) by ring,
        Real.cos_neg]
      exact hcos₂
    have h₁ := shared_AL_gap_bound (p right) (p (src 0)) g₁
      hrightInnerLo hrightHi hlow0 hq0low hsepRight0 hcos₁ hg₁.le
    have h₂ := shared_HL_gap_bound (p (src 1)) (p (src 0)) g₂
      (by linarith [hq1high]) hupper1 hlow0 hq0low
      (by simpa [dist_comm] using hsep01) hcos₂rev hg₂.le
    have hcos₃rev : Real.cos (polarArg (p (src 2)) -
        polarArg (p (src 1))) = Real.cos g₃ := by
      rw [show polarArg (p (src 2)) - polarArg (p (src 1)) =
        -(polarArg (p (src 1)) - polarArg (p (src 2))) by ring,
        Real.cos_neg]
      exact hcos₃
    have h₃ := shared_HL_gap_bound (p (src 1)) (p (src 2)) g₃
      (by linarith [hq1high]) hupper1 hlow2 hq2low
      hsep12 hcos₃ hg₃.le
    have h₄ := shared_AL_gap_bound (p left) (p (src 2)) g₄
      hleftInnerLo hleftHi hlow2 hq2low hsep2Left hcos₄ hg₄.le
    refine ⟨g₁, g₂, g₃, g₄, hsum, Or.inl ?_⟩
    exact ⟨h₁, h₂, h₃, h₄⟩
  · have hw2 : src (2 : Fin 3) = w := by simpa using hcw
    have hq2high : 2 < ‖p (src 2)‖ := by rw [hw2]; exact hwHigh
    have hq0low : ‖p (src 0)‖ ≤ 2 := by
      apply hnotHighOther (0 : Fin 3) (hsrcSpec 0).1
      intro heq
      have hidx : (2 : Fin 3) = 0 := hsrcInj (hw2.trans heq.symm)
      exact (by decide : (2 : Fin 3) ≠ 0) hidx
    have hq1low : ‖p (src 1)‖ ≤ 2 := by
      apply hnotHighOther (1 : Fin 3) (hsrcSpec 1).1
      intro heq
      have hidx : (2 : Fin 3) = 1 := hsrcInj (hw2.trans heq.symm)
      exact (by decide : (2 : Fin 3) ≠ 1) hidx
    have hcos₃rev : Real.cos (polarArg (p (src 2)) -
        polarArg (p (src 1))) = Real.cos g₃ := by
      rw [show polarArg (p (src 2)) - polarArg (p (src 1)) =
        -(polarArg (p (src 1)) - polarArg (p (src 2))) by ring,
        Real.cos_neg]
      exact hcos₃
    have h₁ := shared_AL_gap_bound (p right) (p (src 0)) g₁
      hrightInnerLo hrightHi hlow0 hq0low hsepRight0 hcos₁ hg₁.le
    have h₂ := shared_LL_gap_bound (p (src 0)) (p (src 1)) g₂
      hlow0 hq0low hlow1 hq1low hsep01 hcos₂ hg₂.le
    have h₃ := shared_HL_gap_bound (p (src 2)) (p (src 1)) g₃
      (by linarith [hq2high]) hupper2 hlow1 hq1low
      (by simpa [dist_comm] using hsep12) hcos₃rev hg₃.le
    have h₄ := shared_AH60_gap_bound (p left) (p (src 2)) g₄
      hleftLo hleftHi (by linarith [hq2high]) hupper2
      hsep2Left hcos₄ hg₄.le
    refine ⟨g₁, g₂, g₃, g₄, hsum, Or.inr (Or.inr ?_)⟩
    exact ⟨h₁, h₂, h₃, h₄⟩

/-- The shared-blocker branch closes once its actual contacts, K=9,m=2
counting data, and selected radial caps are supplied. The six cyclic
gaps are built from the four actual touching centers and the two actual
non-outer targets; both the contact-angle spread and endpoint charge are
derived from their geometry. -/
theorem shared_blocker_actual_impossible
    (p : Fin 15 → Plane) (b s : ℝ) (anchor x z : Fin 15)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK9 : (boundarySet p b).card = 9)
    (hm2 : (nonOuterIndices p b).card = 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
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
    (htouchLow : ∀ k, k ∈ touchingInnerSet p b →
      (29 / 20 : ℝ) ≤ ‖p k‖)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b) :
    False := by
  have hysqNorm : (16 / 3 : ℝ) < ‖p anchor‖ ^ 2 := by
    rw [hy]
    exact hysq
  have hs : 2 < s := by
    have hnonneg := norm_nonneg (p anchor)
    nlinarith [hysqNorm]
  have hcore := strict_shared_targets_radius_gt_27_div_25
    (p x) (p z) (p anchor) hysqNorm
    (by rw [hy]; exact hanchorHi) hxy hzy hblockx hblockz
    (hpack.2 x z hxz)
  have hFsmall := F_lt_1301_div_1000_of_le_candidateB b hb hbB
  have hxhi : ‖p x‖ ≤ (1301 / 1000 : ℝ) :=
    (hFcap x hx.1 hx.2).trans hFsmall.le
  have hzhi : ‖p z‖ ≤ (1301 / 1000 : ℝ) :=
    (hFcap z hz.1 hz.2).trans hFsmall.le
  obtain ⟨left, right, g₀, g₅, hLR, hleftNeg, hrightPos,
      hg₀, hg₅, hcharge, hno, hTcard⟩ :=
    shared_actual_hcharge p b s anchor x z hb hbB hpack hK9 hm2
      hx hz hxz hanchorT hy hysq hanchorHi hxy hzy hblockx hblockz
      hhighCard hotherHigh htouchLow hFcap
  have hleftNoOuter : ¬TouchesOuter p b left := by
    rcases hLR with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa [hl] using hx.2
    · simpa [hl] using hz.2
  have hrightNoOuter : ¬TouchesOuter p b right := by
    rcases hLR with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa [hr] using hz.2
    · simpa [hr] using hx.2
  have hleftLo : (27 / 25 : ℝ) ≤ ‖p left‖ := by
    rcases hLR with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa [hl] using hcore.1.le
    · simpa [hl] using hcore.2.le
  have hrightLo : (27 / 25 : ℝ) ≤ ‖p right‖ := by
    rcases hLR with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa [hr] using hcore.2.le
    · simpa [hr] using hcore.1.le
  have hleftHi : ‖p left‖ ≤ 1301 / 1000 := by
    rcases hLR with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa [hl] using hxhi
    · simpa [hl] using hzhi
  have hrightHi : ‖p right‖ ≤ 1301 / 1000 := by
    rcases hLR with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa [hr] using hzhi
    · simpa [hr] using hxhi
  have hleftContact : dist (p left) (p anchor) = 2 := by
    rcases hLR with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa [hl] using hxy
    · simpa [hl] using hzy
  have hrightContact : dist (p right) (p anchor) = 2 := by
    rcases hLR with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa [hr] using hzy
    · simpa [hr] using hxy
  have hleftSector := shared_blocker_target_sector_lt_pi_div_three
    p anchor left hysqNorm hleftContact
  have hrightSector := shared_blocker_target_sector_lt_pi_div_three
    p anchor right hysqNorm hrightContact
  obtain ⟨g₁, g₂, g₃, g₄, hsum, hpattern⟩ :=
    shared_actual_middle_gap_data p b anchor left right g₀ g₅
      hpack hanchorT (by rw [hy]; nlinarith [hysq])
      (by rw [hy]; exact hanchorHi)
      hleftNoOuter hrightNoOuter hleftLo hleftHi hrightLo hrightHi
      hleftNeg hrightPos hleftSector hrightSector hg₀ hg₅ hno hTcard
      hhighCard hotherHigh htouchLow
  have hanchorInner : ‖p anchor‖ < b := by
    have hdata : ‖p anchor‖ < b ∧ TouchesOuter p b anchor := by
      simpa [touchingInnerSet] using hanchorT
    exact hdata.1
  have hanchorD := hD anchor hanchorInner
  have hrec : 4 / candidateB ≤ 4 / b := by
    apply (div_le_div_iff₀ candidateB_pos (by linarith : (0 : ℝ) < b)).2
    nlinarith [hbB]
  have hDmonotone : D b ≤ D candidateB := by
    unfold D
    linarith
  have hsD : s ≤ D candidateB := by
    rw [← hy]
    exact le_of_lt (hanchorD.trans_le hDmonotone)
  have hcross := strict_shared_contacts_cross_negative
    (p x) (p z) (p anchor)
    (by rw [hy]; nlinarith [hanchorHi])
    hxy hzy hblockx hblockz (hpack.2 x z hxz)
  have hδx := shared_contact_delta_domain (p x) (p anchor) s hs hy hxy
    hblockx (by
      intro hz0
      rw [hz0, zero_mul] at hcross
      norm_num at hcross)
  have hδz := shared_contact_delta_domain (p z) (p anchor) s hs hy hzy
    hblockz (by
      intro hz0
      rw [hz0, mul_zero] at hcross
      norm_num at hcross)
  have hspread := shared_contact_angle_spread (p x) (p z) (p anchor) s
    hs hy hxy hzy hblockx hblockz hcross (hpack.2 x z hxz)
  exact shared_six_gap_impossible_of_offset_support
    s (sharedContactDelta s (p anchor) (p x))
    (sharedContactDelta s (p anchor) (p z)) g₀ g₁ g₂ g₃ g₄ g₅
    hs hsD hδx.2.1.le hδz.2.1.le hspread hsum hcharge hpattern

end CP15
