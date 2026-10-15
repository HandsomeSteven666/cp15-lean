import CP15.M2TangentialSelection

open scoped InnerProductSpace Topology

namespace CP15

/-- Second variation matters when the first radial variation vanishes.
For every nonzero velocity with nonnegative radial derivative, the
maximum-sum representative has a strictly obstructing active contact.
All inactive pairs and the containing disk are handled by continuity. -/
theorem exists_active_support_of_nonnegative_variation
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (i : Fin n) (hi : ‖p i‖ < b)
    (v : Plane) (hv : 0 ≤ ⟪p i, v⟫_ℝ) (hvne : v ≠ 0) :
    ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      0 < ⟪p j - p i, v⟫_ℝ := by
  classical
  by_contra hnone
  let x := p i
  have hno (j : Fin n) (hji : j ≠ i)
      (hc : dist x (p j) = 2) :
      ⟪p j - x, v⟫_ℝ ≤ 0 := by
    by_contra hbad
    exact hnone ⟨j, hji, hc, lt_of_not_ge hbad⟩
  have hpath : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnormevent : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖x + t • v‖ < b := by
    have htend : Filter.Tendsto (fun t : ℝ => ‖x + t • v‖)
        (𝓝 0) (𝓝 ‖x‖) := by
      simpa only [zero_smul, add_zero] using hpath.norm.tendsto 0
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (htend.eventually (eventually_lt_nhds hi))
  have hpairevent : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∀ j : Fin n, j ≠ i → 2 ≤ dist (x + t • v) (p j) := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hji))
    · exact (eventually_linear_pair_separated x (p j) v
        (hpack.2 i j (Ne.symm hji)) (hno j hji)).mono (fun _ ht _ => ht)
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
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have hquadratic : 0 < t ^ 2 * ‖v‖ ^ 2 := by positivity
    have hlinear : 0 ≤ t * ⟪x, v⟫_ℝ := mul_nonneg ht.le hv
    have hnormsq := norm_add_sq_real x (t • v)
    have hsq : ‖x‖ ^ 2 < ‖z‖ ^ 2 := by
      dsimp [z]
      rw [hnormsq]
      simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs]
      nlinarith [sq_abs t]
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
        simpa [q, z, Function.update_of_ne hki] using hpairs k hki
      · by_cases hki : k = i
        · subst k
          simpa [q, z, Function.update_of_ne hji, dist_comm] using hpairs j hji
        · simpa [q, Function.update_of_ne hji, Function.update_of_ne hki]
            using hpack.2 j k hjk
  exact no_feasible_single_radius_increase_of_maximal p b hK hS
    i hi z hfar hqpack

theorem quarterTurn_ne_zero {x : Plane} (hx : x ≠ 0) :
    quarterTurn x ≠ 0 := by
  intro h
  apply hx
  ext i
  have h0 := congrArg (fun z : Plane => z 0) h
  have h1 := congrArg (fun z : Plane => z 1) h
  fin_cases i
  · simpa [quarterTurn] using h1
  · have : -(x 1) = 0 := by simpa [quarterTurn] using h0
    simpa using this

/-- The selected representative has contacts on both open sides of
every nonzero inner radial ray. No lower radius, radial cap, absence of
outer contacts, or collinearity assumption is needed. -/
theorem inner_has_two_sided_contacts_of_maximal
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b)
    (i : Fin n) (hi : ‖p i‖ < b) (hx : p i ≠ 0) :
    (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      0 < planeCross (p i) (p j - p i)) ∧
    (∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      planeCross (p i) (p j - p i) < 0) := by
  have hvne := quarterTurn_ne_zero hx
  constructor
  · obtain ⟨j, hji, hc, hdot⟩ :=
      exists_active_support_of_nonnegative_variation p b hpack hK hS
        i hi (quarterTurn (p i)) (by rw [inner_quarterTurn]) hvne
    exact ⟨j, hji, hc, by simpa [inner_quarterTurn_eq_cross] using hdot⟩
  · obtain ⟨j, hji, hc, hdot⟩ :=
      exists_active_support_of_nonnegative_variation p b hpack hK hS
        i hi (-quarterTurn (p i))
        (by simp only [inner_neg_right, inner_quarterTurn, neg_zero]; exact le_rfl)
        (neg_ne_zero.mpr hvne)
    refine ⟨j, hji, hc, ?_⟩
    rw [inner_neg_right, inner_quarterTurn_eq_cross] at hdot
    linarith

/-- At an inner center equal to the origin, every nonzero direction
has an active contact with strictly positive projection. In particular
the contact set cannot lie in a closed semicircle. -/
theorem origin_has_strict_directional_contact
    {n : ℕ} (p : Fin n → Plane) (b : ℝ)
    (hpack : InDisk b p ∧ Separated p 2)
    (hK : MaxBoundaryCount p b) (hS : MaxSumAtBoundaryCount p b)
    (i : Fin n) (hi : ‖p i‖ < b) (hzero : p i = 0)
    (v : Plane) (hvne : v ≠ 0) :
    ∃ j, j ≠ i ∧ ‖p j‖ = 2 ∧ 0 < ⟪p j, v⟫_ℝ := by
  obtain ⟨j, hji, hc, hdot⟩ :=
    exists_active_support_of_nonnegative_variation p b hpack hK hS
      i hi v (by simp [hzero]) hvne
  exact ⟨j, hji, by simpa [hzero, dist_comm] using hc,
    by simpa [hzero] using hdot⟩

end CP15
