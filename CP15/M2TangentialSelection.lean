import CP15.M2Residual

open scoped InnerProductSpace Topology

namespace CP15

/-- Maximum boundary count and then maximum radius sum prohibit replacing
one strictly inner center by a strictly farther feasible point. This is
the selection premise needed for tangential, as well as radial, moves. -/
theorem no_feasible_single_radius_increase_of_maximal
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (i : Fin n) (hi : ‖p i‖ < b)
    (z : Plane) (hfar : ‖p i‖ < ‖z‖) :
    ¬(InDisk b (Function.update p i z) ∧
      Separated (Function.update p i z) 2) := by
  intro hfeas
  let q := Function.update p i z
  have hnewle : ‖z‖ ≤ b := by
    simpa [q] using hfeas.1 i
  have hnewlt : ‖z‖ < b := by
    by_contra hnot
    have hnewEq : ‖z‖ = b :=
      le_antisymm hnewle (le_of_not_gt hnot)
    exact (noBoundaryReplacement_of_maxBoundaryCount p b hK)
      i z hi hnewEq hfeas
  have hboundary : boundarySet q b = boundarySet p b := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [boundarySet, q, ne_of_lt hi, ne_of_lt hnewlt]
    · simp [boundarySet, q, hji]
  have hsumle := hS q hfeas.1 hfeas.2 hboundary
  have herase :
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖q j‖) =
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖p j‖) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [q, Function.update_of_ne hji]
  have hqsum : radiusSum q =
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖p j‖) + ‖z‖ := by
    rw [radiusSum, ← Finset.sum_erase_add Finset.univ
      (fun j => ‖q j‖) (Finset.mem_univ i)]
    simpa [q, herase] using congrArg (fun v : ℝ => v + ‖q i‖) herase
  have hpsum : radiusSum p =
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖p j‖) +
        ‖p i‖ := by
    exact (Finset.sum_erase_add Finset.univ (fun j => ‖p j‖)
      (Finset.mem_univ i)).symm
  rw [hqsum, hpsum] at hsumle
  linarith

/-- Exact first variation of squared pair distance for an arbitrary
linear velocity. -/
theorem linear_move_sq (x y v : Plane) (t : ℝ) :
    ‖x + t • v - y‖ ^ 2 = ‖x - y‖ ^ 2 +
      2 * t * ⟪x - y, v⟫_ℝ + t ^ 2 * ‖v‖ ^ 2 := by
  have heq : x + t • v - y = (x - y) + t • v := by abel
  rw [heq, norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs]
  nlinarith [sq_abs t]

theorem eventually_linear_pair_separated
    (x y v : Plane) (hsep : 2 ≤ dist x y)
    (hno : dist x y = 2 → ⟪y - x, v⟫_ℝ ≤ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 2 ≤ dist (x + t • v) y := by
  by_cases hc : dist x y = 2
  · have hdot := hno hc
    have hbase : ‖x - y‖ ^ 2 = 4 := by
      rw [← dist_eq_norm, hc]
      norm_num
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hsq : 4 ≤ ‖x + t • v - y‖ ^ 2 := by
      rw [linear_move_sq, hbase]
      have hlin : 0 ≤ t * ⟪x - y, v⟫_ℝ := by
        have heq : ⟪x - y, v⟫_ℝ = -⟪y - x, v⟫_ℝ := by
          rw [← neg_sub y x, inner_neg_left]
        rw [heq]
        nlinarith [mul_nonneg ht.le (neg_nonneg.mpr hdot)]
      nlinarith [sq_nonneg t, sq_nonneg ‖v‖]
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x + t • v - y)]
  · have hgt : 2 < dist x y := lt_of_le_of_ne hsep (Ne.symm hc)
    have hpath : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hcont : Continuous (fun t : ℝ => dist (x + t • v) y) :=
      hpath.dist continuous_const
    have hev : ∀ᶠ t : ℝ in 𝓝 0, 2 < dist (x + t • v) y := by
      have htend : Filter.Tendsto
          (fun t : ℝ => dist (x + t • v) y)
          (𝓝 0) (𝓝 (dist x y)) := by
        simpa only [zero_smul, add_zero] using hcont.tendsto 0
      exact htend.eventually (eventually_gt_nhds hgt)
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev).mono
      (fun _ ht => ht.le)

/-- A positive-radius velocity must encounter an active contact with
positive first-order obstruction. This uses the retained maximum-sum
tie-break and includes all inactive contacts via continuity. -/
theorem exists_active_support_of_maximal
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (i : Fin n) (hi : ‖p i‖ < b)
    (v : Plane) (hv : 0 < ⟪p i, v⟫_ℝ) :
    ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      0 < ⟪p j - p i, v⟫_ℝ := by
  by_contra hnone
  let x := p i
  have hno (j : Fin n) (hji : j ≠ i)
      (hc : dist x (p j) = 2) :
      ⟪p j - x, v⟫_ℝ ≤ 0 := by
    by_contra hbad
    exact hnone ⟨j, hji, hc, lt_of_not_ge hbad⟩
  have hpath : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnormcont : Continuous (fun t : ℝ => ‖x + t • v‖) :=
    hpath.norm
  have hnormevent : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖x + t • v‖ < b := by
    have htend : Filter.Tendsto (fun t : ℝ => ‖x + t • v‖)
        (𝓝 0) (𝓝 ‖x‖) := by
      simpa only [zero_smul, add_zero] using hnormcont.tendsto 0
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (htend.eventually (eventually_lt_nhds hi))
  have hpairevent : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∀ j : Fin n, j ≠ i → 2 ≤ dist (x + t • v) (p j) := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hji))
    · exact (eventually_linear_pair_separated x (p j) v
        (hpack.2 i j (Ne.symm hji)) (hno j hji)).mono
          (fun _ ht _ => ht)
  have hchoose : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < t ∧ ‖x + t • v‖ < b ∧
        (∀ j : Fin n, j ≠ i → 2 ≤ dist (x + t • v) (p j)) := by
    filter_upwards [self_mem_nhdsWithin, hnormevent, hpairevent]
      with t ht hbd hpairs
    exact ⟨ht, hbd, hpairs⟩
  obtain ⟨t, ht, hbd, hpairs⟩ := hchoose.exists
  let z := x + t • v
  let q := Function.update p i z
  have hfar : ‖p i‖ < ‖z‖ := by
    have hnormsq := norm_add_sq_real x (t • v)
    have hsq : ‖x‖ ^ 2 < ‖z‖ ^ 2 := by
      dsimp [z]
      rw [hnormsq]
      have hvprod : 0 < t * ⟪x, v⟫_ℝ := mul_pos ht hv
      have hq : 0 ≤ ‖t • v‖ ^ 2 := sq_nonneg _
      rw [real_inner_smul_right]
      nlinarith
    dsimp [x] at hsq
    nlinarith [norm_nonneg (p i), norm_nonneg z]
  have hqpack : InDisk b q ∧ Separated q 2 := by
    constructor
    · intro j
      by_cases hji : j = i
      · subst j
        simpa [q, z] using hbd.le
      · simpa [q, Function.update_of_ne hji] using hpack.1 j
    · intro j k hjk
      by_cases hji : j = i
      · subst j
        have hki : k ≠ i := Ne.symm hjk
        simpa [q, z, Function.update_of_ne hki]
          using hpairs k hki
      · by_cases hki : k = i
        · subst k
          have hdist := hpairs j hji
          simpa [q, z, Function.update_of_ne hji, dist_comm] using hdist
        · simpa [q, Function.update_of_ne hji,
            Function.update_of_ne hki] using hpack.2 j k hjk
  exact no_feasible_single_radius_increase_of_maximal p b hK hS
    i hi z hfar hqpack

/-- Quarter-turn of a plane vector, used to distinguish its two angular
sides without choosing an angle branch. -/
def quarterTurn (x : Plane) : Plane := !₂[-x 1, x 0]

theorem inner_quarterTurn (x : Plane) :
    ⟪x, quarterTurn x⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  simp [quarterTurn, Fin.sum_univ_two]
  ring

theorem inner_quarterTurn_eq_cross (x w : Plane) :
    ⟪w, quarterTurn x⟫_ℝ = planeCross x w := by
  rw [PiLp.inner_apply]
  simp [quarterTurn, planeCross, Fin.sum_univ_two]
  ring

/-- Purely finite gap between local stationarity and a one-sided contact
set. The zero-cross case is an explicit premise; its geometric discharge
is separate. -/
theorem exists_positive_cross_contact_of_maximal
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (i : Fin n) (hi : ‖p i‖ < b) (hx : p i ≠ 0)
    (hzero : ∀ j, j ≠ i → dist (p i) (p j) = 2 →
      planeCross (p i) (p j - p i) = 0 →
        ⟪p j - p i, p i⟫_ℝ ≤ 0) :
    ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      0 < planeCross (p i) (p j - p i) := by
  by_contra hnone
  have hcross (j : Fin n) (hji : j ≠ i)
      (hc : dist (p i) (p j) = 2) :
      planeCross (p i) (p j - p i) ≤ 0 := by
    by_contra hbad
    exact hnone ⟨j, hji, hc, lt_of_not_ge hbad⟩
  have hchoices : ∀ᶠ M : ℝ in Filter.atTop,
      ∀ j : Fin n, j ≠ i → dist (p i) (p j) = 2 →
        ⟪p j - p i, p i⟫_ℝ +
          M * planeCross (p i) (p j - p i) ≤ 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hji))
    by_cases hc : dist (p i) (p j) = 2
    · let a := ⟪p j - p i, p i⟫_ℝ
      let c := planeCross (p i) (p j - p i)
      have hcle : c ≤ 0 := hcross j hji hc
      by_cases hc0 : c = 0
      · exact Filter.Eventually.of_forall (fun M _ _ => by
          dsimp [a, c] at *
          simpa [hc0] using hzero j hji hc hc0)
      · have hclt : c < 0 := lt_of_le_of_ne hcle hc0
        have hevent := Filter.eventually_ge_atTop (a / (-c))
        exact hevent.mono (fun M hM _ _ => by
          have hnc : 0 < -c := by linarith
          have hdiv : a = (a / (-c)) * (-c) := by
            field_simp
          dsimp [a, c] at *
          nlinarith [mul_nonneg (sub_nonneg.mpr hM) hnc.le])
    · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (hc h))
  obtain ⟨M, hM⟩ := hchoices.exists
  let v := p i + M • quarterTurn (p i)
  have hv : 0 < ⟪p i, v⟫_ℝ := by
    have hsq : ⟪p i, p i⟫_ℝ = ‖p i‖ ^ 2 := real_inner_self_eq_norm_sq _
    simp only [v, inner_add_right, real_inner_smul_right,
      inner_quarterTurn, mul_zero, add_zero, hsq]
    exact sq_pos_of_ne_zero (by simpa [norm_eq_zero] using hx)
  obtain ⟨j, hji, hc, hdot⟩ :=
    exists_active_support_of_maximal p b hpack hK hS i hi v hv
  have hformula : ⟪p j - p i, v⟫_ℝ =
      ⟪p j - p i, p i⟫_ℝ +
        M * planeCross (p i) (p j - p i) := by
    simp [v, inner_add_right, real_inner_smul_right,
      inner_quarterTurn_eq_cross]
  rw [hformula] at hdot
  exact (not_lt_of_ge (hM j hji hc)) hdot

/-- An exact contact on the radial line, with the other center closer
than `|x|+2`, must point inward. -/
theorem collinear_contact_points_inward
    (x y : Plane) (hx : x ≠ 0)
    (hc : dist x y = 2)
    (hcross : planeCross x (y - x) = 0)
    (hy : ‖y‖ < ‖x‖ + 2) :
    ⟪y - x, x⟫_ℝ < 0 := by
  let w := y - x
  have hw : ‖w‖ = 2 := by
    simpa [w, dist_eq_norm, norm_sub_rev] using hc
  have hself : ⟪w, w⟫_ℝ = 4 := by
    rw [real_inner_self_eq_norm_sq, hw]
    norm_num
  have hidentity := plane_dot_cross_identity x w w
  rw [hcross, hself] at hidentity
  have hdot : ⟪x, w⟫_ℝ = ⟪w, x⟫_ℝ := real_inner_comm _ _
  have hnormsq : ‖y‖ ^ 2 = ‖x‖ ^ 2 +
      2 * ⟪w, x⟫_ℝ + 4 := by
    have heq : y = x + w := by dsimp [w]; abel
    rw [heq, norm_add_sq_real, ← hdot, hw]
    ring
  have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hysq : ‖y‖ ^ 2 < (‖x‖ + 2) ^ 2 := by
    nlinarith [norm_nonneg y]
  by_contra hnot
  have hdnonneg : 0 ≤ ⟪w, x⟫_ℝ := le_of_not_gt hnot
  have hdle : ⟪w, x⟫_ℝ < 2 * ‖x‖ := by
    nlinarith
  nlinarith [sq_nonneg (⟪w, x⟫_ℝ - 2 * ‖x‖)]

theorem nonOuter_collinear_contact_inward
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ j, ‖p j‖ < b → ‖p j‖ < D b)
    (i : Fin n) (hi : ‖p i‖ < b)
    (hno : ¬TouchesOuter p b i) (hx : p i ≠ 0)
    (hmargin : D b < ‖p i‖ + 2)
    (j : Fin n) (hji : j ≠ i)
    (hc : dist (p i) (p j) = 2)
    (hcross : planeCross (p i) (p j - p i) = 0) :
    ⟪p j - p i, p i⟫_ℝ < 0 := by
  have hjinner : ‖p j‖ < b := by
    by_contra hnot
    have hjbd : ‖p j‖ = b :=
      le_antisymm (hpack.1 j) (le_of_not_gt hnot)
    exact hno ⟨j, hji, hjbd, hc⟩
  exact collinear_contact_points_inward (p i) (p j) hx hc hcross
    ((hD j hjinner).trans hmargin)

/-- One angular side is now certified for any non-outer center whose
radial cap leaves no outward collinear contact. -/
theorem nonOuter_has_positive_cross_contact
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (hD : ∀ j, ‖p j‖ < b → ‖p j‖ < D b)
    (i : Fin n) (hi : ‖p i‖ < b)
    (hno : ¬TouchesOuter p b i) (hx : p i ≠ 0)
    (hmargin : D b < ‖p i‖ + 2) :
    ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      0 < planeCross (p i) (p j - p i) := by
  exact exists_positive_cross_contact_of_maximal p b hpack hK hS i hi hx
    (fun j hji hc hcross =>
      (nonOuter_collinear_contact_inward p b hpack hD i hi hno hx
        hmargin j hji hc hcross).le)

/-- The clockwise counterpart of the finite one-sided stationarity
argument. -/
theorem exists_negative_cross_contact_of_maximal
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (i : Fin n) (hi : ‖p i‖ < b) (hx : p i ≠ 0)
    (hzero : ∀ j, j ≠ i → dist (p i) (p j) = 2 →
      planeCross (p i) (p j - p i) = 0 →
        ⟪p j - p i, p i⟫_ℝ ≤ 0) :
    ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      planeCross (p i) (p j - p i) < 0 := by
  by_contra hnone
  have hcross (j : Fin n) (hji : j ≠ i)
      (hc : dist (p i) (p j) = 2) :
      0 ≤ planeCross (p i) (p j - p i) := by
    by_contra hbad
    exact hnone ⟨j, hji, hc, lt_of_not_ge hbad⟩
  have hchoices : ∀ᶠ M : ℝ in Filter.atTop,
      ∀ j : Fin n, j ≠ i → dist (p i) (p j) = 2 →
        ⟪p j - p i, p i⟫_ℝ -
          M * planeCross (p i) (p j - p i) ≤ 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hji))
    by_cases hc : dist (p i) (p j) = 2
    · let a := ⟪p j - p i, p i⟫_ℝ
      let c := planeCross (p i) (p j - p i)
      have hcle : 0 ≤ c := hcross j hji hc
      by_cases hc0 : c = 0
      · exact Filter.Eventually.of_forall (fun M _ _ => by
          dsimp [a, c] at *
          simpa [hc0] using hzero j hji hc hc0)
      · have hclt : 0 < c := lt_of_le_of_ne hcle (Ne.symm hc0)
        have hevent := Filter.eventually_ge_atTop (a / c)
        exact hevent.mono (fun M hM _ _ => by
          have hdiv : a = (a / c) * c := by field_simp
          dsimp [a, c] at *
          nlinarith [mul_nonneg (sub_nonneg.mpr hM) hclt.le])
    · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (hc h))
  obtain ⟨M, hM⟩ := hchoices.exists
  let v := p i - M • quarterTurn (p i)
  have hv : 0 < ⟪p i, v⟫_ℝ := by
    have hsq : ⟪p i, p i⟫_ℝ = ‖p i‖ ^ 2 := real_inner_self_eq_norm_sq _
    simp only [v, inner_sub_right, real_inner_smul_right,
      inner_quarterTurn, mul_zero, sub_zero, hsq]
    exact sq_pos_of_ne_zero (by simpa [norm_eq_zero] using hx)
  obtain ⟨j, hji, hc, hdot⟩ :=
    exists_active_support_of_maximal p b hpack hK hS i hi v hv
  have hformula : ⟪p j - p i, v⟫_ℝ =
      ⟪p j - p i, p i⟫_ℝ -
        M * planeCross (p i) (p j - p i) := by
    simp [v, inner_sub_right, real_inner_smul_right,
      inner_quarterTurn_eq_cross]
  rw [hformula] at hdot
  exact (not_lt_of_ge (hM j hji hc)) hdot

theorem nonOuter_has_negative_cross_contact
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (hD : ∀ j, ‖p j‖ < b → ‖p j‖ < D b)
    (i : Fin n) (hi : ‖p i‖ < b)
    (hno : ¬TouchesOuter p b i) (hx : p i ≠ 0)
    (hmargin : D b < ‖p i‖ + 2) :
    ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      planeCross (p i) (p j - p i) < 0 := by
  exact exists_negative_cross_contact_of_maximal p b hpack hK hS i hi hx
    (fun j hji hc hcross =>
      (nonOuter_collinear_contact_inward p b hpack hD i hi hno hx
        hmargin j hji hc hcross).le)

/-- Kernel-checked two-sided contact lemma at the precise geometric
premises used for both `K=9,m=2` branches. -/
theorem nonOuter_has_two_sided_contacts
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (hD : ∀ j, ‖p j‖ < b → ‖p j‖ < D b)
    (i : Fin n) (hi : ‖p i‖ < b)
    (hno : ¬TouchesOuter p b i) (hx : p i ≠ 0)
    (hmargin : D b < ‖p i‖ + 2) :
    (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      0 < planeCross (p i) (p j - p i)) ∧
    (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      planeCross (p i) (p j - p i) < 0) := by
  exact ⟨nonOuter_has_positive_cross_contact p b hpack hK hS hD
    i hi hno hx hmargin,
    nonOuter_has_negative_cross_contact p b hpack hK hS hD
      i hi hno hx hmargin⟩

/-- In an `m ≥ 2` configuration, the cap on the other non-outer center
automatically supplies the `|x|+2>D` margin. -/
theorem m2_nonOuter_two_sided_contacts
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (hD : ∀ j, ‖p j‖ < b → ‖p j‖ < D b)
    (hFcap : ∀ j, ‖p j‖ < b → ¬TouchesOuter p b j →
      ‖p j‖ ≤ F b)
    (i j : Fin 15) (hij : i ≠ j)
    (hi : ‖p i‖ < b ∧ ¬TouchesOuter p b i)
    (hj : ‖p j‖ < b ∧ ¬TouchesOuter p b j) :
    (∃ k, k ≠ i ∧ dist (p i) (p k) = 2 ∧
      0 < planeCross (p i) (p k - p i)) ∧
    (∃ k, k ≠ i ∧ dist (p i) (p k) = 2 ∧
      planeCross (p i) (p k - p i) < 0) := by
  have hFsmall := F_lt_1301_div_1000_of_le_candidateB b hb hbB
  have hjrad : ‖p j‖ < 1301 / 1000 :=
    (hFcap j hj.1 hj.2).trans_lt hFsmall
  have hdist := hpack.2 i j hij
  have htri : dist (p i) (p j) ≤ ‖p i‖ + ‖p j‖ := by
    simpa [dist_eq_norm] using norm_sub_le (p i) (p j)
  have hirad : 699 / 1000 < ‖p i‖ := by linarith
  have hDmax := D_lt_twelve_fifths_of_le_candidateB b
    (by linarith) hbB
  have hmargin : D b < ‖p i‖ + 2 := by linarith
  have hx : p i ≠ 0 := by
    intro hzero
    norm_num [hzero] at hirad
  exact nonOuter_has_two_sided_contacts p b hpack hK hS hD
    i hi.1 hi.2 hx hmargin

end CP15
