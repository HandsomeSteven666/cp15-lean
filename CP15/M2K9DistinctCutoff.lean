import CP15.M2K9DistinctGeometry
import CP15.M2K9AngleBounds

set_option maxHeartbeats 0

namespace CP15

open scoped InnerProductSpace

private noncomputable def cutoffB : ℝ := 87 / 25

private theorem cos_13pi_div_72_gt_cutoff_corner :
    contactCos cutoffB (223 / 100) < Real.cos (13 * Real.pi / 72) := by
  let l : ℝ := 13 * (3141592 / 1000000 : ℝ) / 144
  let u : ℝ := 13 * (3141593 / 1000000 : ℝ) / 144
  have hθ0 : (0 : ℝ) ≤ 13 * Real.pi / 72 := by positivity
  have hθ2 : 13 * Real.pi / 72 ≤ 2 := by nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (13 * Real.pi / 72) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (13 * Real.pi / 72) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval _ l u (contactCos cutoffB (223 / 100))
    hθ0 hθ2 hl0 hlx hxu hu1 (by dsimp [l, u, contactCos, cutoffB]; norm_num)

private theorem cos_7pi_div_40_gt_cutoff_corner :
    contactCos cutoffB (43 / 20) < Real.cos (7 * Real.pi / 40) := by
  let l : ℝ := 7 * (3141592 / 1000000 : ℝ) / 80
  let u : ℝ := 7 * (3141593 / 1000000 : ℝ) / 80
  have hθ0 : (0 : ℝ) ≤ 7 * Real.pi / 40 := by positivity
  have hθ2 : 7 * Real.pi / 40 ≤ 2 := by nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (7 * Real.pi / 40) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (7 * Real.pi / 40) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval _ l u (contactCos cutoffB (43 / 20))
    hθ0 hθ2 hl0 hlx hxu hu1 (by dsimp [l, u, contactCos, cutoffB]; norm_num)

private theorem cutoff_F_mono (b : ℝ) (hb : 17 / 5 < b)
    (hbb : b ≤ cutoffB) : F b ≤ F cutoffB := by
  have hbpos : 0 < b := by linarith
  have hBpos : 0 < cutoffB := by norm_num [cutoffB]
  have hrec : 4 / cutoffB ≤ 4 / b := by
    rw [div_le_div_iff₀ hBpos hbpos]
    nlinarith
  have hD : D b ≤ D cutoffB := by
    unfold D
    linarith
  have hDbpos : 0 ≤ D b := by
    unfold D
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hbpos]
    nlinarith [hb]
  have hDBpos : 0 ≤ D cutoffB := by
    unfold D
    norm_num [cutoffB]
  have hsquare : D b ^ 2 - 4 ≤ D cutoffB ^ 2 - 4 := by
    nlinarith
  unfold F
  exact Real.sqrt_le_sqrt hsquare

/-- With two distinct high-radius contacts, every uncharged outer gap can
be charged a chosen angular threshold instead of the coarser `4/7`. -/
theorem exists_distinct_two_contact_threshold_budget
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hK : (boundarySet p b).card = 9)
    (hsize : 2 ≤ (boundaryAngles p b).card)
    (inner outer : Fin 2 → Fin 15)
    (hinj : Function.Injective inner)
    (hinner : ∀ c, ‖p (inner c)‖ < b)
    (hradius : ∀ c, 2 ≤ ‖p (inner c)‖)
    (houter : ∀ c, ‖p (outer c)‖ = b)
    (htouch : ∀ c, dist (p (inner c)) (p (outer c)) = 2)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hbsmall : b * Real.sin (θ / 2) < 1) :
    ∃ charge : Fin 2 → Fin (boundaryAngles p b).card,
    ∃ δ : Fin 2 → ℝ,
      Function.Injective charge ∧
      (∀ c, (47 / 100 : ℝ) < δ c ∧
        2 * δ c ≤ nextBoundaryGap p b hsize (charge c) ∧
        2 * ‖p (inner c)‖ * b * Real.cos (δ c) =
          b ^ 2 + ‖p (inner c)‖ ^ 2 - 4 ∧
        δ c = Real.arccos
          ((b ^ 2 + ‖p (inner c)‖ ^ 2 - 4) /
            (2 * ‖p (inner c)‖ * b))) ∧
      (∑ c : Fin 2, 2 * δ c) + 7 * θ ≤ 2 * Real.pi := by
  classical
  have hKle : 9 ≤ (boundarySet p b).card := by rw [hK]
  obtain ⟨charge, δ, hcharge, hdata, hbudget, hexact⟩ :=
    exists_large_contact_exact_gap_budget p b hb hbB hpack.2 hD hKle
      inner outer hinj hinner hradius houter htouch
  have hsubset : Finset.univ.image charge ⊆
      (Finset.univ : Finset (Fin (boundaryAngles p b).card)) := by simp
  have hbase (u : Fin (boundaryAngles p b).card) :
      θ ≤ nextBoundaryGap p b hsize u :=
    every_next_gap_ge_threshold p b θ (by linarith) hθ0 hθpi hbsmall
      hpack.2 hsize u
  have hbudgetθ := injective_gap_budget Finset.univ charge
    (fun c => 2 * δ c) (nextBoundaryGap p b hsize) θ (2 * Real.pi)
    hcharge hsubset (fun c => (hdata c).2.1)
    (fun u _ => hbase u) (sum_next_boundary_gaps p b hsize)
  have hangleCount : (boundaryAngles p b).card = 9 := by
    rw [boundaryAngles_card p b hpack.2]
    exact hK
  have hchargeCount : (Finset.univ.image charge).card = 2 := by
    rw [Finset.card_image_of_injective _ hcharge]
    simp
  have hremain :
      (Finset.univ \ Finset.univ.image charge).card = 7 := by
    rw [Finset.card_sdiff_of_subset hsubset, Finset.card_univ]
    simp [hangleCount, hchargeCount]
  have hconstant :
      (∑ _u ∈ Finset.univ \ Finset.univ.image charge, θ) = 7 * θ := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hremain]
    norm_num
  rw [hconstant] at hbudgetθ
  refine ⟨charge, δ, hcharge, ?_, hbudgetθ⟩
  intro c
  exact ⟨(hdata c).1, (hdata c).2.1,
    (hdata c).2.2, hexact c⟩

private theorem cutoff_contact_offset_gt_angle
    (b l s δ θ : ℝ)
    (hb3 : 3 < b) (hbb : b ≤ cutoffB)
    (hls0 : 0 < l) (hls : l ≤ s) (hsupper : s ≤ 12 / 5)
    (hδ0 : 0 ≤ δ) (hδpi : δ ≤ Real.pi)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hcorner : contactCos cutoffB l < Real.cos θ)
    (hlaw : 2 * s * b * Real.cos δ = b ^ 2 + s ^ 2 - 4) :
    θ < δ := by
  have hcos := contact_offset_cos_le_rational_corner b cutoffB l s δ
    hb3 hbb (by norm_num [cutoffB]) hls0 hls hsupper hlaw
  by_contra hnot
  have hδθ : δ ≤ θ := le_of_not_gt hnot
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hδ0 hθpi hδθ
  linarith

private theorem cutoff_gap_threshold_admissible (b : ℝ)
    (hbpos : 0 < b) (hbb : b ≤ cutoffB) :
    b * Real.sin ((3339 * Real.pi / 18000) / 2) < 1 := by
  let θ : ℝ := 3339 * Real.pi / 18000
  let l : ℝ := 3339 * (3141592 / 1000000 : ℝ) / 36000
  let u : ℝ := 3339 * (3141593 / 1000000 : ℝ) / 36000
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ θ / 2 := by
    dsimp [l, θ]
    nlinarith [Real.pi_gt_d6]
  have hxu : θ / 2 ≤ u := by
    dsimp [u, θ]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  have hx0 : 0 ≤ θ / 2 := by dsimp [θ]; positivity
  have hx1 : θ / 2 ≤ 1 := hxu.trans hu1
  have hsin0 : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0
      (by linarith [Real.pi_gt_three])
  have hsinbound := Real.sin_bound
    (x := θ / 2) (by simpa [abs_of_nonneg hx0] using hx1)
  have hsinpoly : Real.sin (θ / 2) ≤ sinCubicUpper (θ / 2) := by
    have h := (abs_le.mp hsinbound).2
    rw [abs_of_nonneg hx0] at h
    dsimp [sinCubicUpper]
    linarith
  have hlow3 : l ^ 3 ≤ (θ / 2) ^ 3 :=
    pow_le_pow_left₀ hl0 hlx 3
  have hhigh5 : (θ / 2) ^ 5 ≤ u ^ 5 :=
    pow_le_pow_left₀ hx0 hxu 5
  have hpolyUpper : sinCubicUpper (θ / 2) ≤
      u - l ^ 3 / 6 + u ^ 5 / 100 := by
    dsimp [sinCubicUpper]
    nlinarith
  have hU0 : 0 ≤ u - l ^ 3 / 6 + u ^ 5 / 100 :=
    le_trans hsin0 (le_trans hsinpoly hpolyUpper)
  have hUprod : cutoffB * (u - l ^ 3 / 6 + u ^ 5 / 100) < 1 := by
    dsimp [u, l, cutoffB]
    norm_num
  calc
    b * Real.sin (θ / 2) ≤ b * (u - l ^ 3 / 6 + u ^ 5 / 100) :=
      mul_le_mul_of_nonneg_left (hsinpoly.trans hpolyUpper) hbpos.le
    _ ≤ cutoffB * (u - l ^ 3 / 6 + u ^ 5 / 100) :=
      mul_le_mul_of_nonneg_right hbb hU0
    _ < 1 := hUprod

private theorem strict_blocker_sq_radius
    (x y : Plane) (hcontact : dist x y = 2)
    (hstrict : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ) :
    4 + ‖x‖ ^ 2 < ‖y‖ ^ 2 := by
  have hdist : ‖x - y‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hcontact]
    norm_num
  rw [norm_sub_sq_real] at hdist
  have hinner : ⟪x, y⟫_ℝ = ⟪y, x⟫_ℝ := real_inner_comm _ _
  nlinarith [hdist, hstrict]

/-- The exact outer-gap support and contact geometry exclude `b ≤ 87/25`
for two distinct strict blockers. This is the first part of the stronger
`b > 7/2` interval reduction, now replayed in Lean. -/
theorem distinct_m2_K9_requires_b_gt_87_div_25
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (hK9 : (boundarySet p b).card = 9)
    (hm2 : (nonOuterIndices p b).card = 2)
    (target blocker outer : Fin 2 → Fin 15)
    (htarget : Function.Injective target)
    (hno : ∀ c, ‖p (target c)‖ < b ∧
      ¬TouchesOuter p b (target c))
    (hdata : ∀ c, blocker c ≠ target c ∧
      dist (p (target c)) (p (blocker c)) = 2 ∧
      ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
      outer c ≠ blocker c ∧ ‖p (outer c)‖ = b ∧
      dist (p (blocker c)) (p (outer c)) = 2 ∧
      ‖p (target c)‖ ^ 2 <
        ⟪p (blocker c), p (target c)⟫_ℝ)
    (hblockerNe : blocker 0 ≠ blocker 1) :
    cutoffB < b := by
  have hm2le : 2 ≤ (nonOuterIndices p b).card := by rw [hm2]
  have hb17 := m2_radius_gt_seventeen_fifths p b hb hpack hD hblock
    hFcap hFsmall hm2le
  by_contra hnot
  have hbcut : b ≤ cutoffB := le_of_not_gt hnot
  have hFmon := cutoff_F_mono b hb17 hbcut
  have hF0sq : F cutoffB ^ 2 = D cutoffB ^ 2 - 4 := by
    unfold F
    exact Real.sq_sqrt (by norm_num [D, cutoffB])
  have hF0nonneg : 0 ≤ F cutoffB := Real.sqrt_nonneg _
  have hF0lt : F cutoffB < 6 / 5 := by
    have hsquare : D cutoffB ^ 2 - 4 < (6 / 5 : ℝ) ^ 2 := by
      norm_num [D, cutoffB]
    nlinarith [hF0sq]
  have htargetHi (c : Fin 2) : ‖p (target c)‖ ≤ F b :=
    hFcap (target c) (hno c).1 (hno c).2
  have htargetSep : 2 ≤ dist (p (target 0)) (p (target 1)) :=
    hpack.2 _ _ (htarget.ne (by decide))
  have htargetTri : dist (p (target 0)) (p (target 1)) ≤
      ‖p (target 0)‖ + ‖p (target 1)‖ := by
    simpa [dist_eq_norm] using norm_sub_le (p (target 0)) (p (target 1))
  have htargetSum : (2 : ℝ) ≤
      ‖p (target 0)‖ + ‖p (target 1)‖ := htargetSep.trans htargetTri
  have hbig : 1 ≤ ‖p (target 0)‖ ∨ 1 ≤ ‖p (target 1)‖ := by
    by_contra h
    push_neg at h
    linarith
  have hblockerInj : Function.Injective blocker := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hblockerNe]
  have hsize : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hpack.2, hK9]
    norm_num
  have hDhi : D b < 12 / 5 :=
    D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB
  have hinner (c : Fin 2) : ‖p (blocker c)‖ < b := (hdata c).2.2.1
  have hradius (c : Fin 2) : 2 ≤ ‖p (blocker c)‖ :=
    (hdata c).2.2.2.1.le
  have houter (c : Fin 2) : ‖p (outer c)‖ = b :=
    (hdata c).2.2.2.2.2.1
  have htouch (c : Fin 2) :
      dist (p (blocker c)) (p (outer c)) = 2 :=
    (hdata c).2.2.2.2.2.2.1
  let θ : ℝ := 3339 * Real.pi / 18000
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hθpi : θ ≤ Real.pi := by
    dsimp [θ]
    nlinarith [Real.pi_pos]
  have hbpos : 0 < b := by linarith
  have hbsmall := cutoff_gap_threshold_admissible b hbpos hbcut
  obtain ⟨charge, δ, hcharge, hδdata, hbudget⟩ :=
    exists_distinct_two_contact_threshold_budget p b hb hbB hpack hD
      hK9 hsize blocker outer hblockerInj hinner hradius houter htouch
      θ hθ0 hθpi hbsmall
  have hoffPi (c : Fin 2) : δ c ≤ Real.pi := by
    have hgap := every_next_gap_lt_pi p b (by linarith) hbB hpack.2
      (by omega) (charge c)
    linarith [(hδdata c).2.1]
  have hlargeRoot (c : Fin 2) (hc : 1 ≤ ‖p (target c)‖) :
      Real.sqrt 5 ≤ ‖p (blocker c)‖ := by
    have hcontact := (hdata c).2.1
    have hstrict := (hdata c).2.2.2.2.2.2.2
    have hsq := strict_blocker_sq_radius (p (target c))
      (p (blocker c)) hcontact hstrict
    have hradicand : 5 ≤ 4 + ‖p (target c)‖ ^ 2 := by nlinarith
    have hroot : Real.sqrt 5 ≤ Real.sqrt (4 + ‖p (target c)‖ ^ 2) :=
      Real.sqrt_le_sqrt hradicand
    have hrootLt : Real.sqrt (4 + ‖p (target c)‖ ^ 2) <
        ‖p (blocker c)‖ := by
      have hsqroot := Real.sq_sqrt
        (show 0 ≤ 4 + ‖p (target c)‖ ^ 2 by positivity)
      nlinarith [hsqroot, hsq, Real.sqrt_nonneg (4 + ‖p (target c)‖ ^ 2),
        norm_nonneg (p (blocker c))]
    linarith
  have hF0sqVal : F cutoffB ^ 2 =
      (6772261 / 4730625 : ℝ) := by
    norm_num [D, cutoffB] at hF0sq ⊢
    exact hF0sq
  have hF0lower : (119 / 100 : ℝ) < F cutoffB := by
    nlinarith [hF0sqVal, hF0nonneg]
  have hlowRoot : (43 / 20 : ℝ) <
      Real.sqrt (4 + (2 - F cutoffB) ^ 2) := by
    have hsqrt := Real.sq_sqrt
      (show 0 ≤ 4 + (2 - F cutoffB) ^ 2 by positivity)
    have hmargin : (4 / 5 : ℝ) < 2 - F cutoffB := by linarith [hF0lt]
    have hrad : (43 / 20 : ℝ) ^ 2 < 4 + (2 - F cutoffB) ^ 2 := by
      nlinarith [sq_nonneg ((2 - F cutoffB) - 4 / 5)]
    nlinarith [hsqrt, hrad, Real.sqrt_nonneg (4 + (2 - F cutoffB) ^ 2)]
  have hsmallRoot (c d : Fin 2) (hcd : c ≠ d)
      (hc : 1 ≤ ‖p (target c)‖) :
      (43 / 20 : ℝ) < ‖p (blocker d)‖ := by
    have hrlo : 2 - F cutoffB ≤ ‖p (target d)‖ := by
      have hhi : ‖p (target c)‖ ≤ F cutoffB :=
        (htargetHi c).trans hFmon
      have hsumCD : (2 : ℝ) ≤
          ‖p (target c)‖ + ‖p (target d)‖ := by
        fin_cases c <;> fin_cases d
        · exact False.elim (hcd rfl)
        · simpa using htargetSum
        · simpa [add_comm] using htargetSum
        · exact False.elim (hcd rfl)
      linarith [hsumCD, hhi]
    have hr0 : 0 ≤ 2 - F cutoffB := by linarith [hF0lt]
    have hradicand :
        4 + (2 - F cutoffB) ^ 2 ≤ 4 + ‖p (target d)‖ ^ 2 := by
      nlinarith [norm_nonneg (p (target d)), hrlo, hr0]
    have hrootle := Real.sqrt_le_sqrt hradicand
    have hsq := strict_blocker_sq_radius (p (target d))
      (p (blocker d)) ((hdata d).2.1)
      ((hdata d).2.2.2.2.2.2.2)
    have hrootlt : Real.sqrt (4 + ‖p (target d)‖ ^ 2) <
        ‖p (blocker d)‖ := by
      have hsqrt := Real.sq_sqrt
        (show 0 ≤ 4 + ‖p (target d)‖ ^ 2 by positivity)
      nlinarith [hsqrt, hsq, Real.sqrt_nonneg (4 + ‖p (target d)‖ ^ 2),
        norm_nonneg (p (blocker d))]
    linarith
  have hthetaBig (c : Fin 2) (hc : 1 ≤ ‖p (target c)‖) :
      13 * Real.pi / 72 < δ c := by
    have hsupper : ‖p (blocker c)‖ ≤ 12 / 5 :=
      (lt_trans (hD (blocker c) (hinner c)) hDhi).le
    have hsqrt5 : (223 / 100 : ℝ) < Real.sqrt 5 := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
      nlinarith [Real.sqrt_nonneg (5 : ℝ)]
    exact cutoff_contact_offset_gt_angle b (223 / 100)
      ‖p (blocker c)‖ (δ c) (13 * Real.pi / 72)
      (by linarith) hbcut (by norm_num)
      (le_of_lt (lt_of_lt_of_le hsqrt5 (hlargeRoot c hc)))
      hsupper (by linarith [(hδdata c).1]) (hoffPi c)
      (by positivity) (by nlinarith [Real.pi_pos])
      cos_13pi_div_72_gt_cutoff_corner (hδdata c).2.2.1
  have hthetaSmall (c d : Fin 2) (hc : 1 ≤ ‖p (target c)‖)
      (hcd : c ≠ d) : 7 * Real.pi / 40 < δ d := by
    have hsupper : ‖p (blocker d)‖ ≤ 12 / 5 :=
      (lt_trans (hD (blocker d) (hinner d)) hDhi).le
    exact cutoff_contact_offset_gt_angle b (43 / 20)
      ‖p (blocker d)‖ (δ d) (7 * Real.pi / 40)
      (by linarith) hbcut (by norm_num) (by exact le_of_lt (hsmallRoot c d hcd hc))
      hsupper (by linarith [(hδdata d).1]) (hoffPi d)
      (by positivity) (by nlinarith [Real.pi_pos])
      cos_7pi_div_40_gt_cutoff_corner (hδdata d).2.2.1
  rw [Fin.sum_univ_two] at hbudget
  rcases hbig with h0 | h1
  · have hsmall := hthetaSmall 0 1 h0 (by decide)
    dsimp [θ] at hbudget
    have hlarge := hthetaBig 0 h0
    nlinarith [hbudget, hlarge, hsmall, Real.pi_pos]
  · have hsmall := hthetaSmall 1 0 h1 (by decide)
    have hbig1 := hthetaBig 1 h1
    dsimp [θ] at hbudget
    nlinarith [hbudget, hbig1, hsmall, Real.pi_pos]

end CP15
