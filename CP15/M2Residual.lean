import CP15.M2K8Closure

open scoped InnerProductSpace

namespace CP15

/-- Under the checked selected-representative hypotheses, `m = 2`
forces exactly nine boundary centers. -/
theorem m2_requires_K9
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ i, ‖p i‖ < b → ‖p i‖ < D b)
    (hFcap : ∀ i, ‖p i‖ < b → ¬TouchesOuter p b i → ‖p i‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ i, ‖p i‖ < b → p i ≠ 0 →
      ∃ j, j ≠ i ∧ dist (p i) (p j) = 2 ∧
        ‖p i‖ ^ 2 < ⟪p j, p i⟫_ℝ)
    (hm2 : 2 ≤ (nonOuterIndices p b).card)
    (hmle : (nonOuterIndices p b).card ≤ 2) :
    (boundarySet p b).card = 9 := by
  have hKle := boundary_count_le_ten p b (by linarith) hbB hpack.2
  by_cases hK8 : (boundarySet p b).card ≤ 8
  · exact False.elim (m2_impossible_at_K_le_8 p b hb hbB hpack
      hD hFcap hFsmall hblock hK8 hm2 hmle)
  by_cases hK9 : (boundarySet p b).card = 9
  · exact hK9
  have hK10 : 10 ≤ (boundarySet p b).card := by omega
  exact False.elim (m2_impossible_at_K10 p b hb hbB hpack
    hD hFcap hFsmall hblock hK10 hm2)

/-- The exact remaining incidence split at `K = 9`. Both branches retain
actual strict contacts and actual outer contacts. In the shared branch the
blocker has squared radius above `16/3`; in the distinct branch its two
outer contacts pay an injective cyclic gap budget. -/
theorem m2_K9_shared_or_distinct_budget
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
    (hm2 : 2 ≤ (nonOuterIndices p b).card) :
    ∃ target blocker outer : Fin 2 → Fin 15,
      Function.Injective target ∧
      (∀ c, ‖p (target c)‖ < b ∧
        ¬TouchesOuter p b (target c)) ∧
      (∀ c, blocker c ≠ target c ∧
        dist (p (target c)) (p (blocker c)) = 2 ∧
        ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
        outer c ≠ blocker c ∧ ‖p (outer c)‖ = b ∧
        dist (p (blocker c)) (p (outer c)) = 2 ∧
        ‖p (target c)‖ ^ 2 <
          ⟪p (blocker c), p (target c)⟫_ℝ) ∧
      ((blocker 0 = blocker 1 ∧
          (16 / 3 : ℝ) < ‖p (blocker 0)‖ ^ 2 ∧
          2 * Real.sqrt 3 < b) ∨
        (blocker 0 ≠ blocker 1 ∧
          (∑ c : Fin 2, 2 * Real.arccos
            ((b ^ 2 + ‖p (blocker c)‖ ^ 2 - 4) /
              (2 * ‖p (blocker c)‖ * b))) +
            (((boundaryAngles p b).card : ℝ) - 2) * (4 / 7) ≤
              2 * Real.pi)) := by
  classical
  obtain ⟨target, blocker, outer, htarget, hno, hdata⟩ :=
    m2_selected_blockers p b hb hbB hpack hD hFcap hFsmall hblock
      (by omega) hm2
  refine ⟨target, blocker, outer, htarget, hno, hdata, ?_⟩
  by_cases hsame : blocker 0 = blocker 1
  · left
    have hsq := selected_shared_blocker_sq_gt_sixteen_thirds
      p hpack.2 target blocker htarget
      (fun c => (hdata c).2.1)
      (fun c => (hdata c).2.2.2.2.2.2.2)
      0 1 (by decide) hsame
    have hDgt : (16 / 3 : ℝ) < D b ^ 2 := by
      have hd := hD (blocker 0) (hdata 0).2.2.1
      have hn := norm_nonneg (p (blocker 0))
      nlinarith
    have hrad : 0 ≤ D b ^ 2 - 4 := by linarith
    have hFsq : F b ^ 2 = D b ^ 2 - 4 := by
      unfold F
      exact Real.sq_sqrt hrad
    have hbcut := radius_gt_two_sqrt_three_of_F_sq b hb (by linarith)
    exact ⟨hsame, hsq, hbcut⟩
  · right
    have hinj : Function.Injective blocker := by
      intro c d h
      fin_cases c <;> fin_cases d <;> simp_all
    have hbudget := large_contact_arccos_card_budget p b hb hbB
      hpack.2 hD (by omega) blocker outer hinj
      (fun c => (hdata c).2.2.1)
      (fun c => (hdata c).2.2.2.1.le)
      (fun c => (hdata c).2.2.2.2.2.1)
      (fun c => (hdata c).2.2.2.2.2.2.1)
    exact ⟨hsame, by simpa using hbudget⟩

/-- The strongest current selected-optimum statement: either `m ≤ 1`
already, or the sole unclosed row is `K = 9, m = 2`. -/
theorem exists_optimal_selected_with_m_le_one_or_K9_m2 :
    ∃ b : ℝ, ∃ p : Fin 15 → Plane,
      b ≤ candidateB ∧ CenterOptimal 15 b ∧
      InDisk b p ∧ Separated p 2 ∧
      ((nonOuterIndices p b).card ≤ 1 ∨
        ((nonOuterIndices p b).card = 2 ∧
          (boundarySet p b).card = 9)) := by
  obtain ⟨b, p, hbB, hopt, hp, hs, hD, hblock, hFcap, hFsmall, _⟩ :=
    exists_optimal_selected_full
  have hb : 2 < b := centerFeasible_radius_gt_two hopt.1
  have hK := boundary_count_le_ten p b (by linarith) hbB hs
  have hmle : (nonOuterIndices p b).card ≤ 2 := by
    by_contra hnot
    exact m3_impossible_at_K_le_ten p b hb hbB ⟨hp, hs⟩ hD
      hFcap hFsmall hblock hK (by omega)
  by_cases hm1 : (nonOuterIndices p b).card ≤ 1
  · exact ⟨b, p, hbB, hopt, hp, hs, Or.inl hm1⟩
  have hm2 : 2 ≤ (nonOuterIndices p b).card := by omega
  have hK9 := m2_requires_K9 p b hb hbB ⟨hp, hs⟩
    hD hFcap hFsmall hblock hm2 hmle
  exact ⟨b, p, hbB, hopt, hp, hs, Or.inr ⟨by omega, hK9⟩⟩

end CP15
