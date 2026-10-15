import CP15.M2K9DistinctActualWord

namespace CP15

open scoped InnerProductSpace

/-- Polar form of the oriented area determinant. -/
theorem planeCross_polar (x y : Plane) :
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
  rw [planeCross, Real.sin_sub]
  rw [← hxc, ← hxs, ← hyc, ← hys]
  ring

/-- The cyclic arc between two points in the sorted six-angle list. -/
theorem distinctForwardArc_range
    (φ : Fin 6 → ℝ) (hmono : StrictMono φ)
    (hrange : ∀ i, -Real.pi ≤ φ i ∧ φ i ≤ Real.pi)
    (a b : Fin 6) :
    0 ≤ distinctForwardArc φ a b ∧
      distinctForwardArc φ a b ≤ 2 * Real.pi := by
  by_cases hab : a.val < b.val
  · have hφab : φ a ≤ φ b := (hmono (by omega)).le
    constructor
    · simpa [distinctForwardArc, hab] using sub_nonneg.mpr hφab
    · simp [distinctForwardArc, hab]
      have ha := (hrange a).1
      have hb := (hrange b).2
      linarith
  · by_cases hba : b.val < a.val
    · have hφba : φ b < φ a := hmono (by omega)
      constructor
      · simp only [distinctForwardArc, if_neg (not_lt_of_gt hba)]
        have hb := (hrange b).1
        have ha := (hrange a).2
        linarith
      · simp only [distinctForwardArc, if_neg (not_lt_of_gt hba)]
        linarith
    · have hab' : a = b := by
        apply Fin.ext
        omega
      subst b
      have hd : distinctForwardArc φ a a = 2 * Real.pi := by
        simp [distinctForwardArc]
      rw [hd]
      exact ⟨by nlinarith [Real.pi_pos], le_rfl⟩

/-- The two directed arcs between distinct entries of the sorted list
sum to one turn. -/
theorem distinctForwardArc_complement
    (φ : Fin 6 → ℝ) (a b : Fin 6) (hab : a ≠ b) :
    distinctForwardArc φ a b + distinctForwardArc φ b a =
      2 * Real.pi := by
  by_cases hlt : a.val < b.val
  · simp [distinctForwardArc, hlt, not_lt_of_gt hlt]
  · have hgt : b.val < a.val := by
      have hv : a.val ≠ b.val := by
        intro heq
        exact hab (Fin.ext heq)
      omega
    simp [distinctForwardArc, not_lt_of_gt hgt, hgt]

/-- Sine of the lifted cyclic arc agrees with the difference of polar
arguments, including the wrap-around case. -/
theorem distinctForwardArc_sin
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (a b : Fin 6) :
    Real.sin (polarArg (q b) - polarArg (q a)) =
      Real.sin (distinctForwardArc φ a b) := by
  rw [harg a, harg b]
  by_cases heq : a = b
  · subst b
    simp [distinctForwardArc]
  · by_cases hab : a.val < b.val
    · simp [distinctForwardArc, hab]
    · have hba : b.val < a.val := by
        have hv : a.val ≠ b.val := by
          intro hval
          exact heq (Fin.ext hval)
        omega
      have harc : distinctForwardArc φ a b =
          (φ b - φ a) + 2 * Real.pi := by
        simp [distinctForwardArc, not_lt_of_gt hba]
        ring
      rw [harc, Real.sin_add_two_pi]

/-- Cosine of the lifted arc is the cosine of the endpoint polar
separation. -/
theorem distinctForwardArc_cos
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (a b : Fin 6) (hab : a ≠ b) :
    Real.cos (polarArg (q a) - polarArg (q b)) =
      Real.cos (distinctForwardArc φ a b) := by
  rw [harg a, harg b]
  by_cases hlt : a.val < b.val
  · have heq : φ a - φ b = -(φ b - φ a) := by ring
    rw [heq, Real.cos_neg]
    simp [distinctForwardArc, hlt]
  · have hgt : b.val < a.val := by
      have hv : a.val ≠ b.val := by
        intro hval
        exact hab (Fin.ext hval)
      omega
    have heq : φ a - φ b =
        2 * Real.pi - (φ b + 2 * Real.pi - φ a) := by ring
    rw [heq, Real.cos_two_pi_sub]
    simp [distinctForwardArc, not_lt_of_gt hgt]

/-- A negative cross product makes the clockwise arc strictly shorter
than a semicircle. -/
theorem distinct_negative_cross_backward_arc_lt_pi
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hmono : StrictMono φ)
    (hrange : ∀ i, -Real.pi ≤ φ i ∧ φ i ≤ Real.pi)
    (a j : Fin 6) (haj : a ≠ j)
    (ha : 0 < ‖q a‖) (hj : 0 < ‖q j‖)
    (hcross : planeCross (q a) (q j - q a) < 0) :
    distinctForwardArc φ j a < Real.pi := by
  have harc_range := distinctForwardArc_range φ hmono hrange a j
  have hcross_expand : planeCross (q a) (q j - q a) =
      planeCross (q a) (q j) := by
    rw [planeCross]
    simp [planeCross]
    ring
  have hpolar := planeCross_polar (q a) (q j)
  have hsin : Real.sin (distinctForwardArc φ a j) < 0 := by
    rw [hcross_expand, hpolar, distinctForwardArc_sin q φ harg a j] at hcross
    have hprod : 0 < ‖q a‖ * ‖q j‖ := mul_pos ha hj
    nlinarith
  have hforward_gt : Real.pi < distinctForwardArc φ a j := by
    by_contra hnot
    have hle : distinctForwardArc φ a j ≤ Real.pi := le_of_not_gt hnot
    have hsin_nonneg := Real.sin_nonneg_of_nonneg_of_le_pi
      harc_range.1 hle
    linarith
  have hcomp := distinctForwardArc_complement φ a j haj
  have harcpos : 0 ≤ distinctForwardArc φ j a := (distinctForwardArc_range
    φ hmono hrange j a).1
  linarith

/-- The exact contact cosine for an A--L pair is strictly above `-5/8`
when the core radius is at least `699/1000` and the low radius at least
`3/2`. -/
theorem distinct_AL_contact_cos_gt_neg_five_eighths
    (x y : Plane)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖)
    (hylo : (3 / 2 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 2)
    (hcontact : dist x y = 2) :
    -(5 / 8 : ℝ) < Real.cos (polarArg x - polarArg y) := by
  have hxpos : 0 < ‖x‖ := by linarith
  have hypos : 0 < ‖y‖ := by linarith
  have hdist : ‖x - y‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hcontact]
    norm_num
  rw [norm_sub_sq_real] at hdist
  have hpolar := polar_inner x y
  rw [hpolar] at hdist
  have hprod : (699 / 1000 : ℝ) * (3 / 2 : ℝ) ≤
      ‖x‖ * ‖y‖ := by
    exact mul_le_mul hxlo hylo (by norm_num) (by norm_num)
  have hxSq : (699 / 1000 : ℝ) ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg x]
  have hySq : (3 / 2 : ℝ) ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [norm_nonneg y]
  have hpoly : 0 < ‖x‖ ^ 2 + ‖y‖ ^ 2 +
      (5 / 4 : ℝ) * ‖x‖ * ‖y‖ - 4 := by
    norm_num at hxSq hySq hprod ⊢
    nlinarith
  nlinarith [hdist]

/-- Rational Taylor enclosure for the 51 degree cosine threshold used to
turn the A--L contact cosine into an angular upper bound. -/
theorem cos_51pi_div_180_gt_five_eighths :
    (5 / 8 : ℝ) < Real.cos (51 * Real.pi / 180) := by
  let l : ℝ := 51 * (3141592 / 1000000 : ℝ) / 360
  let u : ℝ := 51 * (3141593 / 1000000 : ℝ) / 360
  have hθ0 : (0 : ℝ) ≤ 51 * Real.pi / 180 := by positivity
  have hθ2 : 51 * Real.pi / 180 ≤ (2 : ℝ) := by
    nlinarith [Real.pi_lt_d6]
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hlx : l ≤ (51 * Real.pi / 180) / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hxu : (51 * Real.pi / 180) / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num
  exact cos_gt_of_half_interval _ l u _ hθ0 hθ2 hl0 hlx hxu hu1
    (by dsimp [l, u]; norm_num)

/-- An A--L contact on an arc of at most `pi` subtends less than 129
degrees. The endpoint comparison is exact and uses no decimal angles. -/
theorem distinct_AL_contact_arc_lt_129
    (x y : Plane) (δ : ℝ)
    (hxlo : (699 / 1000 : ℝ) ≤ ‖x‖)
    (hylo : (3 / 2 : ℝ) ≤ ‖y‖)
    (hyhi : ‖y‖ ≤ 2)
    (hcontact : dist x y = 2)
    (hcos : Real.cos δ = Real.cos (polarArg x - polarArg y))
    (hδ0 : 0 ≤ δ) (hδpi : δ ≤ Real.pi) :
    δ < 129 * Real.pi / 180 := by
  have hcontactCos := distinct_AL_contact_cos_gt_neg_five_eighths
    x y hxlo hylo hyhi hcontact
  have h51 := cos_51pi_div_180_gt_five_eighths
  have h129cos : Real.cos (129 * Real.pi / 180) < -(5 / 8 : ℝ) := by
    have heq : 129 * Real.pi / 180 = Real.pi - 51 * Real.pi / 180 := by ring
    rw [heq, Real.cos_pi_sub]
    linarith
  by_contra hnot
  have hθle : 129 * Real.pi / 180 ≤ δ := le_of_not_gt hnot
  have hθpi : 129 * Real.pi / 180 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hθ0 : 0 ≤ 129 * Real.pi / 180 := by positivity
  have hcosle := Real.cos_le_cos_of_nonneg_of_le_pi hθ0 hδpi hθle
  rw [hcos] at hcosle
  linarith

/-- A strict radial blocker at contact has squared radius strictly greater
than four plus the squared target radius. -/
theorem strict_blocker_contact_sq_lower
    (x y : Plane) (hcontact : dist x y = 2)
    (hstrict : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ) :
    4 + ‖x‖ ^ 2 < ‖y‖ ^ 2 := by
  have hdist : ‖x - y‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hcontact]
    norm_num
  rw [norm_sub_sq_real] at hdist
  have hinner : ⟪x, y⟫_ℝ = ⟪y, x⟫_ℝ := real_inner_comm _ _
  nlinarith [hdist, hstrict]

/-- The squared blocker estimate implies the strict root lower bound used
by the radius certificate. -/
theorem strict_blocker_contact_radius_lower
    (x y : Plane) (hcontact : dist x y = 2)
    (hstrict : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ) :
    Real.sqrt (4 + ‖x‖ ^ 2) < ‖y‖ := by
  have hsquare := strict_blocker_contact_sq_lower x y hcontact hstrict
  have hnonneg : 0 ≤ 4 + ‖x‖ ^ 2 := by positivity
  have hroot := Real.sq_sqrt hnonneg
  have hypos : 0 ≤ ‖y‖ := norm_nonneg y
  nlinarith [hroot, hsquare]

/-- The transferred outer contact gives the low-center radius needed by the
129-degree contact split, once the missing outer-radius cutoff is supplied. -/
theorem touching_radius_ge_three_halves
    (p : Fin 15 → Plane) (b : ℝ) (i : Fin 15)
    (hb : (7 / 2 : ℝ) < b) (ht : TouchesOuter p b i) :
    (3 / 2 : ℝ) < ‖p i‖ := by
  obtain ⟨j, _, hj, hc⟩ := ht
  have htri := norm_add_le (p j - p i) (p i)
  rw [sub_add_cancel] at htri
  rw [dist_eq_norm] at hc
  have hswap : ‖p j - p i‖ = 2 := by
    simpa only [norm_sub_rev] using hc
  rw [hj, hswap] at htri
  linarith

/-- In the canonical `AHAHLL` orientation, every opposite-side active
contact from the first core is the last low center; from the second core
it can only be the first high center or the first core. This is a cyclic
angle classification, not a contact-graph enumeration. -/
theorem distinct_AHAHLL_opposite_contact_classification
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ) (w : Fin 6 → M2Kind)
    (hsep : Separated q 2)
    (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (hword : ∀ i, w i = wordAHAHLL i)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L → (3 / 2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (a j : Fin 6)
    (ha : w a = .A) (haj : a ≠ j)
    (hcontact : dist (q a) (q j) = 2)
    (hcross : planeCross (q a) (q j - q a) < 0) :
    (a = 0 ∧ j = 5) ∨ (a = 2 ∧ (j = 0 ∨ j = 1)) := by
  have hrange (i : Fin 6) : -Real.pi ≤ φ i ∧ φ i ≤ Real.pi := by
    rw [← harg i]
    exact ⟨le_of_lt (polarArg_range (q i)).1,
      (polarArg_range (q i)).2⟩
  have hnormA : 0 < ‖q a‖ := by
    have h := hA a ha
    linarith
  have harcshort := distinct_negative_cross_backward_arc_lt_pi q φ harg
    hmono hrange a j haj hnormA (by
      have hsepij : 2 ≤ dist (q a) (q j) := by
        exact hsep a j haj
      have hqpos : 0 < ‖q j‖ := by
        by_contra hn
        have hz : q j = 0 := norm_eq_zero.mp (le_antisymm
          (le_of_not_gt hn) (norm_nonneg _))
        rw [hz] at hsepij
        have ha' := hA a ha
        have hdist : dist (q a) (0 : Plane) = ‖q a‖ := by simp [dist_eq_norm]
        rw [hdist] at hsepij
        linarith
      exact hqpos) (by
        have hcross' : planeCross (q a) (q j - q a) < 0 := hcross
        exact hcross')
  have hA' (i : Fin 6) (hi : wordAHAHLL i = .A) :
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000 := by
    exact hA i ((hword i).trans hi)
  have hH' (i : Fin 6) (hi : wordAHAHLL i = .H) :
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000 := by
    exact hH i ((hword i).trans hi)
  have hL' (i : Fin 6) (hi : wordAHAHLL i = .L) :
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2 := by
    constructor
    · linarith [(hL i ((hword i).trans hi)).1]
    · exact (hL i ((hword i).trans hi)).2
  have hLweak (i : Fin 6) (hi : w i = .L) :
      (7 / 5 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2 := by
    have hh := hL i hi
    exact ⟨by linarith [hh.1], hh.2⟩
  have hgap (i : Fin 6) :
      ((classGapCost (wordAHAHLL i) (wordAHAHLL (i + 1)) : ℕ) : ℝ) *
        Real.pi / 1800 ≤ distinctSixGap φ i := by
    have hc := distinct_gap_cost q hsep φ hmono harg hfirst hlast
      w hA hH hLweak i
    simpa [hword i, hword (i + 1)] using hc
  have hg0 : 49 * Real.pi / 180 ≤ distinctSixGap φ 0 := by
    have hh := hgap 0
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hg1 : 49 * Real.pi / 180 ≤ distinctSixGap φ 1 := by
    have hh := hgap 1
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hg2 : 49 * Real.pi / 180 ≤ distinctSixGap φ 2 := by
    have hh := hgap 2
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hg3 : 53 * Real.pi / 180 ≤ distinctSixGap φ 3 := by
    have hh := hgap 3
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hg4 : Real.pi / 3 ≤ distinctSixGap φ 4 := by
    have hh := hgap 4
    norm_num [wordAHAHLL, classGapCost] at hh ⊢
    nlinarith [hh, Real.pi_pos]
  have hsum := distinctSixGap_sum φ
  rw [Fin.sum_univ_six] at hsum
  have hsum' : distinctSixGap φ 0 + distinctSixGap φ 1 +
      distinctSixGap φ 2 + distinctSixGap φ 3 + distinctSixGap φ 4 +
      distinctSixGap φ 5 = 2 * Real.pi := by
    simpa [distinctSixGap] using hsum
  have hg5pi : distinctSixGap φ 5 < Real.pi := by
    nlinarith [hsum', hg0, hg1, hg2, hg3, hg4, Real.pi_pos]
  have hcos5 : Real.cos (polarArg (q 0) - polarArg (q 5)) =
      Real.cos (distinctSixGap φ 5) := by
    have hc := distinctSixGap_cos_lift q φ harg 5
    have heq : polarArg (q 0) - polarArg (q 5) =
        -(polarArg (q 5) - polarArg (q 0)) := by ring
    rw [heq, Real.cos_neg]
    exact hc
  have hLfive : (7 / 5 : ℝ) ≤ ‖q 5‖ ∧ ‖q 5‖ ≤ 2 := by
    have hh := hL 5 (by simpa [hword 5, wordAHAHLL])
    exact ⟨by linarith [hh.1], hh.2⟩
  have hg5nonneg : 0 ≤ distinctSixGap φ 5 := by
    simp [distinctSixGap]
    nlinarith [hfirst, hlast, Real.pi_pos]
  have hg5 : 59 * Real.pi / 150 < distinctSixGap φ 5 :=
    shared_AL_angle_gt_70_8 (q 0) (q 5) (distinctSixGap φ 5)
      (hA 0 (by simpa [hword 0, wordAHAHLL])).1
      (hA 0 (by simpa [hword 0, wordAHAHLL])).2
      hLfive.1 hLfive.2
      (by simpa [dist_comm] using hsep 0 5 (by decide))
       hcos5 hg5nonneg hg5pi.le
  have hwordA : a = 0 ∨ a = 2 := by
    have ha' : wordAHAHLL a = .A := by rw [← hword a]; exact ha
    fin_cases a <;> simp_all [wordAHAHLL]
  rcases hwordA with rfl | rfl
  · fin_cases j
    · exact False.elim (haj rfl)
    · have hbig : Real.pi < distinctForwardArc φ 1 0 := by
        have heq : distinctForwardArc φ 1 0 =
            distinctSixGap φ 1 + distinctSixGap φ 2 +
              distinctSixGap φ 3 + distinctSixGap φ 4 +
              distinctSixGap φ 5 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg1, hg2, hg3, hg4, hg5, Real.pi_pos]
      have hs : distinctForwardArc φ 1 0 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have hbig : Real.pi < distinctForwardArc φ 2 0 := by
        have heq : distinctForwardArc φ 2 0 =
            distinctSixGap φ 2 + distinctSixGap φ 3 +
              distinctSixGap φ 4 + distinctSixGap φ 5 := by
          simp [distinctForwardArc, distinctSixGap]
        rw [heq]
        nlinarith [hg2, hg3, hg4, hg5, Real.pi_pos]
      have hs : distinctForwardArc φ 2 0 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have hbig : Real.pi < distinctForwardArc φ 3 0 := by
        have heq : distinctForwardArc φ 3 0 =
            distinctSixGap φ 3 + distinctSixGap φ 4 +
              distinctSixGap φ 5 := by
          simp [distinctForwardArc, distinctSixGap]
        rw [heq]
        nlinarith [hg3, hg4, hg5, Real.pi_pos]
      have hs : distinctForwardArc φ 3 0 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have h130 : 129 * Real.pi / 180 < distinctForwardArc φ 4 0 := by
        have heq : distinctForwardArc φ 4 0 =
            distinctSixGap φ 4 + distinctSixGap φ 5 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg4, hg5, Real.pi_pos]
      have hlow := hL 4 (by norm_num [hword 4, wordAHAHLL])
      have hcos : Real.cos (distinctForwardArc φ 4 0) =
          Real.cos (polarArg (q 0) - polarArg (q 4)) := by
        have hc := distinctForwardArc_cos q φ harg 4 0 (by decide)
        have heq : polarArg (q 4) - polarArg (q 0) =
            -(polarArg (q 0) - polarArg (q 4)) := by ring
        rw [heq, Real.cos_neg] at hc
        exact hc.symm
      have hangle := distinct_AL_contact_arc_lt_129 (q 0) (q 4)
        (distinctForwardArc φ 4 0) (hA 0 (by simpa [hword 0, wordAHAHLL])).1
        hlow.1 hlow.2 hcontact hcos
        (distinctForwardArc_range φ hmono hrange 4 0).1 harcshort.le
      exact False.elim (not_lt_of_ge h130.le hangle)
    · exact Or.inl ⟨rfl, rfl⟩
  · fin_cases j
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
    · exact Or.inr ⟨rfl, Or.inr rfl⟩
    · exact False.elim (haj rfl)
    · have hbig : Real.pi < distinctForwardArc φ 3 2 := by
        have heq : distinctForwardArc φ 3 2 =
            distinctSixGap φ 3 + distinctSixGap φ 4 + distinctSixGap φ 5 +
              distinctSixGap φ 0 + distinctSixGap φ 1 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg3, hg4, hg5, hg0, hg1, Real.pi_pos]
      have hs : distinctForwardArc φ 3 2 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have hbig : Real.pi < distinctForwardArc φ 4 2 := by
        have heq : distinctForwardArc φ 4 2 =
            distinctSixGap φ 4 + distinctSixGap φ 5 +
              distinctSixGap φ 0 + distinctSixGap φ 1 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg4, hg5, hg0, hg1, Real.pi_pos]
      have hs : distinctForwardArc φ 4 2 < Real.pi := by
        simpa using harcshort
      exact False.elim ((not_lt_of_ge hbig.le) hs)
    · have h129 : 129 * Real.pi / 180 < distinctForwardArc φ 5 2 := by
        have heq : distinctForwardArc φ 5 2 =
            distinctSixGap φ 5 + distinctSixGap φ 0 +
              distinctSixGap φ 1 := by
          simp [distinctForwardArc, distinctSixGap] <;> ring
        rw [heq]
        nlinarith [hg5, hg0, hg1, Real.pi_pos]
      have hlow := hL 5 (by norm_num [hword 5, wordAHAHLL])
      have hcos : Real.cos (distinctForwardArc φ 5 2) =
          Real.cos (polarArg (q 2) - polarArg (q 5)) := by
        have hc := distinctForwardArc_cos q φ harg 5 2 (by decide)
        have heq : polarArg (q 5) - polarArg (q 2) =
            -(polarArg (q 2) - polarArg (q 5)) := by ring
        rw [heq, Real.cos_neg] at hc
        exact hc.symm
      have hangle := distinct_AL_contact_arc_lt_129 (q 2) (q 5)
        (distinctForwardArc φ 5 2) (hA 2 (by simpa [hword 2, wordAHAHLL])).1
        hlow.1 hlow.2 hcontact hcos
        (distinctForwardArc_range φ hmono hrange 5 2).1 harcshort.le
      exact False.elim (not_lt_of_ge h129.le hangle)

/-- Once the two-sided contact theorem supplies negative-cross contacts,
the canonical cyclic order forces the final contact split: `A₀` contacts
`L₁`, while `A₁` contacts either `A₀` or `H₀`. -/
theorem distinct_AHAHLL_forced_contact_split
    (q : Fin 6 → Plane) (φ : Fin 6 → ℝ) (w : Fin 6 → M2Kind)
    (hsep : Separated q 2)
    (hmono : StrictMono φ)
    (harg : ∀ i, polarArg (q i) = φ i)
    (hfirst : -Real.pi < φ 0) (hlast : φ 5 ≤ Real.pi)
    (hword : ∀ i, w i = wordAHAHLL i)
    (hA : ∀ i, w i = .A →
      (699 / 1000 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 1301 / 1000)
    (hH : ∀ i, w i = .H →
      (2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2385436 / 1000000)
    (hL : ∀ i, w i = .L → (3 / 2 : ℝ) ≤ ‖q i‖ ∧ ‖q i‖ ≤ 2)
    (hneg0 : ∃ j, j ≠ 0 ∧ dist (q 0) (q j) = 2 ∧
      planeCross (q 0) (q j - q 0) < 0)
    (hneg2 : ∃ j, j ≠ 2 ∧ dist (q 2) (q j) = 2 ∧
      planeCross (q 2) (q j - q 2) < 0) :
    dist (q 0) (q 5) = 2 ∧
      (dist (q 2) (q 0) = 2 ∨ dist (q 2) (q 1) = 2) := by
  obtain ⟨j0, hj0, hc0, hcross0⟩ := hneg0
  have hclass0 := distinct_AHAHLL_opposite_contact_classification
    q φ w hsep hmono harg hfirst hlast hword hA hH hL
    0 j0 (by simp [hword 0, wordAHAHLL]) hj0.symm hc0 hcross0
  have hcontact5 : j0 = 5 := by
    rcases hclass0 with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · norm_num at h
  have hfirstContact : dist (q 0) (q 5) = 2 := by
    simpa [hcontact5] using hc0
  obtain ⟨j2, hj2, hc2, hcross2⟩ := hneg2
  have hclass2 := distinct_AHAHLL_opposite_contact_classification
    q φ w hsep hmono harg hfirst hlast hword hA hH hL
    2 j2 (by simp [hword 2, wordAHAHLL]) hj2.symm hc2 hcross2
  have hlastContact : j2 = 0 ∨ j2 = 1 := by
    rcases hclass2 with ⟨h, _⟩ | ⟨_, h⟩
    · norm_num at h
    · exact h
  rcases hlastContact with hzero | hone
  · exact ⟨hfirstContact, Or.inl (by simpa [hzero] using hc2)⟩
  · exact ⟨hfirstContact, Or.inr (by simpa [hone] using hc2)⟩

end CP15
