import CP15.Replacement

open scoped InnerProductSpace Topology

set_option maxHeartbeats 800000

namespace CP15

/-- If a pair is separated and an active contact has no strict radial
blocker, a small positive radial move keeps this pair separated. -/
theorem eventually_radial_pair_separated
    (x y : Plane)
    (hsep : 2 ≤ dist x y)
    (hno : dist x y = 2 → ⟪y, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 2 ≤ dist ((1 + t) • x) y := by
  by_cases hc : dist x y = 2
  · have hdot := hno hc
    have hbase : ‖x - y‖ ^ 2 = 4 := by
      rw [← dist_eq_norm, hc]
      norm_num
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hsq : 4 ≤ ‖(1 + t) • x - y‖ ^ 2 := by
      rw [radial_move_sq x y t ht.le, hbase]
      have hcoeff : 0 ≤ ‖x‖ ^ 2 - ⟪y, x⟫_ℝ := sub_nonneg.mpr hdot
      have hlinear := mul_nonneg ht.le hcoeff
      have hquadratic := mul_nonneg (sq_nonneg t) (sq_nonneg ‖x‖)
      linarith
    rw [dist_eq_norm]
    have hn : 0 ≤ ‖(1 + t) • x - y‖ := norm_nonneg _
    nlinarith
  · have hgt : 2 < dist x y := lt_of_le_of_ne hsep (Ne.symm hc)
    have hpath : Continuous (fun t : ℝ => (1 + t) • x) :=
      (continuous_const.add continuous_id).smul continuous_const
    have hcont : Continuous (fun t : ℝ => dist ((1 + t) • x) y) :=
      hpath.dist continuous_const
    have hev : ∀ᶠ t : ℝ in 𝓝 0, 2 < dist ((1 + t) • x) y := by
      have htend : Filter.Tendsto
          (fun t : ℝ => dist ((1 + t) • x) y)
          (𝓝 0) (𝓝 (dist x y)) := by
        simpa only [add_zero, one_smul] using hcont.tendsto 0
      exact htend.eventually (eventually_gt_nhds hgt)
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev).mono
      (fun _ ht => ht.le)

/-- The exact local maximality premise used by the strict-blocker theorem. -/
def NoFeasibleOutwardMove {n : ℕ} (p : Fin n → Plane) (b : ℝ) : Prop :=
  ∀ i (t : ℝ), 0 < t → p i ≠ 0 → ‖p i‖ < b →
    ¬(InDisk b (Function.update p i ((1 + t) • p i)) ∧
      Separated (Function.update p i ((1 + t) • p i)) 2)

noncomputable def radiusSum {n : ℕ} (p : Fin n → Plane) : ℝ :=
  ∑ i, ‖p i‖

def MaxSumAtBoundaryCount {n : ℕ} (p : Fin n → Plane) (b : ℝ) : Prop :=
  ∀ q : Fin n → Plane,
    InDisk b q → Separated q 2 →
      boundarySet q b = boundarySet p b → radiusSum q ≤ radiusSum p

theorem noFeasibleOutwardMove_of_maximal {n : ℕ}
    (p : Fin n → Plane) (b : ℝ)
    (hK : MaxBoundaryCount p b)
    (hS : MaxSumAtBoundaryCount p b) :
    NoFeasibleOutwardMove p b := by
  intro i t ht hnonzero hinner hfeas
  let q := Function.update p i ((1 + t) • p i)
  have hnewle : ‖(1 + t) • p i‖ ≤ b := by
    simpa [q] using hfeas.1 i
  have hnewlt : ‖(1 + t) • p i‖ < b := by
    by_contra hnot
    have hnewEq : ‖(1 + t) • p i‖ = b :=
      le_antisymm hnewle (le_of_not_gt hnot)
    exact (noBoundaryReplacement_of_maxBoundaryCount p b hK)
      i ((1 + t) • p i) hinner hnewEq hfeas
  have hboundary : boundarySet q b = boundarySet p b := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [boundarySet, q, ne_of_lt hinner, ne_of_lt hnewlt]
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
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖p j‖) +
        ‖(1 + t) • p i‖ := by
    rw [radiusSum, ← Finset.sum_erase_add Finset.univ
      (fun j => ‖q j‖) (Finset.mem_univ i)]
    simpa [q, herase] using congrArg (fun v : ℝ => v + ‖q i‖) herase
  have hpsum : radiusSum p =
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖p j‖) +
        ‖p i‖ := by
    exact (Finset.sum_erase_add Finset.univ (fun j => ‖p j‖)
      (Finset.mem_univ i)).symm
  have hxpos : 0 < ‖p i‖ := norm_pos_iff.mpr hnonzero
  have ht1 : 0 ≤ 1 + t := by linarith
  have hnewnorm : ‖(1 + t) • p i‖ = (1 + t) * ‖p i‖ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht1]
  have hprod : 0 < t * ‖p i‖ := mul_pos ht hxpos
  rw [hqsum, hpsum, hnewnorm] at hsumle
  nlinarith

theorem strict_radial_blocker_of_no_outward_move {n : ℕ}
    (p : Fin n → Plane) (b : ℝ) (i : Fin n)
    (hpack : InDisk b p ∧ Separated p 2)
    (hinner : ‖p i‖ < b) (hnonzero : p i ≠ 0)
    (hmax : NoFeasibleOutwardMove p b) :
    ∃ j : Fin n, j ≠ i ∧ dist (p i) (p j) = 2 ∧
      ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ := by
  by_contra hnone
  let x := p i
  have hno : ∀ j : Fin n, j ≠ i →
      dist x (p j) = 2 → ⟪p j, x⟫_ℝ ≤ ‖x‖ ^ 2 := by
    intro j hji hc
    by_contra hbad
    have hstrict : ‖x‖ ^ 2 < ⟪p j, x⟫_ℝ := lt_of_not_ge hbad
    exact hnone ⟨j, hji, hc, hstrict⟩
  have hpath : Continuous (fun t : ℝ => (1 + t) • x) :=
    (continuous_const.add continuous_id).smul continuous_const
  have hnormcont : Continuous (fun t : ℝ => ‖(1 + t) • x‖) := hpath.norm
  have hnormevent : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖(1 + t) • x‖ < b := by
    have htend : Filter.Tendsto (fun t : ℝ => ‖(1 + t) • x‖)
        (𝓝 0) (𝓝 ‖x‖) := by
      simpa only [add_zero, one_smul] using hnormcont.tendsto 0
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (htend.eventually (eventually_lt_nhds hinner))
  have hpairevent : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∀ j : Fin n, j ≠ i → 2 ≤ dist ((1 + t) • x) (p j) := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hji))
    · exact (eventually_radial_pair_separated x (p j)
        (hpack.2 i j (Ne.symm hji)) (hno j hji)).mono
          (fun _ ht _ => ht)
  have hchoose : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < t ∧ ‖(1 + t) • x‖ < b ∧
        (∀ j : Fin n, j ≠ i → 2 ≤ dist ((1 + t) • x) (p j)) := by
    filter_upwards [self_mem_nhdsWithin, hnormevent, hpairevent]
      with t ht hbd hpairs
    exact ⟨ht, hbd, hpairs⟩
  obtain ⟨t, ht, hbd, hpairs⟩ := hchoose.exists
  let q := Function.update p i ((1 + t) • x)
  have hqpack : InDisk b q ∧ Separated q 2 := by
    constructor
    · intro j
      by_cases hji : j = i
      · subst j
        simpa [q, x] using hbd.le
      · simpa [q, Function.update_of_ne hji] using hpack.1 j
    · intro j k hjk
      by_cases hji : j = i
      · subst j
        have hki : k ≠ i := Ne.symm hjk
        simpa [q, x, Function.update_of_ne hki]
          using hpairs k hki
      · by_cases hki : k = i
        · subst k
          have hdist := hpairs j hji
          simpa [q, x, Function.update_of_ne hji, dist_comm] using hdist
        · simpa [q, Function.update_of_ne hji,
            Function.update_of_ne hki] using hpack.2 j k hjk
  exact hmax i t ht hnonzero hinner hqpack

end CP15
