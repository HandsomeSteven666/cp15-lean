import CP15.ActualDistinctContacts

open scoped InnerProductSpace

namespace CP15

/-- The already closed shared-blocker branch excludes every common
strict blocker of two actual core centers, not merely the particular
blocker pair originally chosen by the selection theorem. -/
theorem SelectedPacking15.no_shared_strict_blocker
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hm2 : (nonOuterIndices p b).card = 2)
    (a z y : Fin 15) (haz : a ≠ z)
    (ha : ‖p a‖ < b ∧ ¬TouchesOuter p b a)
    (hz : ‖p z‖ < b ∧ ¬TouchesOuter p b z)
    (hy : ‖p y‖ < b)
    (hay : dist (p a) (p y) = 2) (hzy : dist (p z) (p y) = 2)
    (hstrictA : ‖p a‖ ^ 2 < ⟪p y, p a⟫_ℝ)
    (hstrictZ : ‖p z‖ ^ 2 < ⟪p y, p z⟫_ℝ) : False := by
  classical
  have hfront := h.two_core_distinct hm2
  have hK9 := hfront.1
  have hbhalf := hfront.2.1
  have hb : 2 < b := by linarith
  have hysq := two_strict_targets_force_blocker_sq_gt_sixteen_thirds
    (p a) (p z) (p y) hay hzy hstrictA hstrictZ (h.separated a z haz)
  have hy2 : 2 < ‖p y‖ := by nlinarith [norm_nonneg (p y)]
  have hyTouch : TouchesOuter p b y := by
    by_contra hn
    have hcap := h.coreCap y hy hn
    have hsqrt : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith [h.coreCapSmall]
  obtain ⟨o, hoy, ho, hyo⟩ := hyTouch
  let target : Fin 2 → Fin 15 := ![a, z]
  let blocker : Fin 2 → Fin 15 := fun _ => y
  let outer : Fin 2 → Fin 15 := fun _ => o
  have htarget : Function.Injective target := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [target]
  have hno (i : Fin 2) : ‖p (target i)‖ < b ∧ ¬TouchesOuter p b (target i) := by
    fin_cases i
    · exact ha
    · exact hz
  have hcontact (i : Fin 2) : dist (p (target i)) (p y) = 2 := by
    fin_cases i
    · exact hay
    · exact hzy
  have hstrict (i : Fin 2) : ‖p (target i)‖ ^ 2 < ⟪p y, p (target i)⟫_ℝ := by
    fin_cases i
    · exact hstrictA
    · exact hstrictZ
  have hdata (i : Fin 2) : blocker i ≠ target i ∧
      dist (p (target i)) (p (blocker i)) = 2 ∧
      ‖p (blocker i)‖ < b ∧ 2 < ‖p (blocker i)‖ ∧
      outer i ≠ blocker i ∧ ‖p (outer i)‖ = b ∧
      dist (p (blocker i)) (p (outer i)) = 2 ∧
      ‖p (target i)‖ ^ 2 < ⟪p (blocker i), p (target i)⟫_ℝ := by
    refine ⟨?_, hcontact i, hy, hy2, hoy, ho, hyo, hstrict i⟩
    intro heq
    have hd := hcontact i
    change y = target i at heq
    rw [← heq, dist_self] at hd
    norm_num at hd
  have hbcut : 2 * Real.sqrt 3 < b := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hn := Real.sqrt_nonneg 3
    nlinarith
  exact m2_K9_shared_impossible p b hb h.belowCandidate ⟨h.inDisk, h.separated⟩
    h.innerCap h.coreCap hK9 hm2 target blocker outer htarget hno hdata
    rfl hysq hbcut

/-- An extra contact to the other core is nonblocking. This discharges
the shared-branch premise used in the final distinct contact alternative. -/
theorem SelectedPacking15.common_contact_radius_nonblocking
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hm2 : (nonOuterIndices p b).card = 2)
    (a z y : Fin 15) (haz : a ≠ z)
    (ha : ‖p a‖ < b ∧ ¬TouchesOuter p b a)
    (hz : ‖p z‖ < b ∧ ¬TouchesOuter p b z)
    (hy : ‖p y‖ < b)
    (hay : dist (p a) (p y) = 2) (hzy : dist (p z) (p y) = 2)
    (hstrictA : ‖p a‖ ^ 2 < ⟪p y, p a⟫_ℝ) :
    ‖p y‖ ^ 2 ≤ 4 + ‖p z‖ ^ 2 := by
  by_contra hn
  have hsq : ‖p z - p y‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hzy]
    norm_num
  rw [norm_sub_sq_real] at hsq
  have hstrictZ : ‖p z‖ ^ 2 < ⟪p y, p z⟫_ℝ := by
    nlinarith [real_inner_comm (p z) (p y)]
  exact h.no_shared_strict_blocker hm2 a z y haz ha hz hy hay hzy hstrictA hstrictZ

end CP15
