import CP15.K9m0Tables

namespace CP15

set_option maxHeartbeats 0

/-- Actual six-center geometry is mapped to seven closed radial bins,
the full cyclic angle budget, and the collision-safe outer cost. The
integer word certificate is therefore applied to a necessary condition
of the original packing, not to an unconnected numerical model. -/
theorem SelectedPacking15.six_touching_K_ge_nine_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : 9 ≤ (boundarySet p b).card)
    (inner : Fin 6 → Fin 15) (hinj : Function.Injective inner)
    (hinner : ∀ i, ‖p (inner i)‖ < b)
    (ht : ∀ i, TouchesOuter p b (inner i)) : False := by
  classical
  have hb : (323 / 100 : ℝ) < b := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sqrt_nonneg 5, h.elementaryLower]
  have hlo (i : Fin 6) : (123 / 100 : ℝ) ≤ ‖p (inner i)‖ := by
    obtain ⟨j, _, hj, hc⟩ := ht i
    have hr := norm_add_le (p j - p (inner i)) (p (inner i))
    have hn : ‖p j - p (inner i)‖ = 2 := by
      simpa [dist_eq_norm, norm_sub_rev] using hc
    rw [sub_add_cancel, hj, hn] at hr
    linarith
  have hhi (i : Fin 6) : ‖p (inner i)‖ ≤ 4771 / 2000 := by
    have hcap := (h.innerCap _ (hinner i)).trans
      (D_lt_shared_high_ceiling b (by linarith) h.belowCandidate)
    linarith
  let q : Fin 6 → Plane := fun i => p (inner i)
  have hsep : Separated q 2 := fun i j hij => h.separated _ _ (hinj.ne hij)
  have hpolar := annular_polarArg_injective q hsep (123 / 100) (4771 / 2000)
    (by norm_num) hlo hhi
  obtain ⟨src, φ, hsrc, hmono, harg, hrange⟩ := exists_sorted_polar_permutation q hpolar
  let ix : Fin 6 → Fin 15 := fun i => inner (src i)
  have hix : Function.Injective ix := hinj.comp hsrc.1
  have hbins (i : Fin 6) := k9_bin_cover ‖p (ix i)‖ (hlo (src i)) (hhi (src i))
  choose w hwLo hwHi using hbins
  have hcost := h.touching_cost_budget (by omega) ix hix
    (fun i => hinner (src i)) (fun i => ht (src i))
  have heachExtra (i : Fin 6) : (k9ExtraUnits (w i) : ℝ) / 10000 ≤
      max 0 (2 * contactAngle b ‖p (ix i)‖ - 57588 / 100000) :=
    k9_bin_extra_lower h (ix i) (hinner (src i)) (ht (src i)) (w i) (hwLo i)
  have hsumExtra := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heachExtra i)
  have hsumExtra' : ((∑ i, k9ExtraUnits (w i) : ℕ) : ℝ) / 10000 ≤
      ∑ i, max 0 (2 * contactAngle b ‖p (ix i)‖ - 57588 / 100000) := by
    simpa [Nat.cast_sum, Finset.sum_div] using hsumExtra
  have hKcast : (9 : ℝ) ≤ ((boundarySet p b).card : ℝ) := by exact_mod_cast hK
  have hExtraReal : ((∑ i, k9ExtraUnits (w i) : ℕ) : ℝ) ≤ 11010 := by
    nlinarith [Real.pi_lt_d6]
  have hExtraNat : (∑ i, k9ExtraUnits (w i)) ≤ 11010 := by exact_mod_cast hExtraReal
  have heachPair (i : Fin 6) : (k9PairUnits (w i) (w (i + 1)) : ℝ) / 10000 ≤
      cyclicAngleGap φ i := by
    apply k9_bin_pair_angle_lower (p (ix i)) (p (ix (i + 1)))
      (cyclicAngleGap φ i) (w i) (w (i + 1)) (hwLo i) (hwHi i)
      (hwLo (i + 1)) (hwHi (i + 1))
      (h.separated _ _ (hix.ne (by fin_cases i <;> decide)))
    · exact cyclicAngleGap_cos (fun i => p (ix i)) φ harg i
    · exact cyclicAngleGap_nonneg φ hmono hrange i
  have hsumPair := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heachPair i)
  rw [cyclicAngleGap_sum] at hsumPair
  have hsumPair' : ((∑ i, k9PairUnits (w i) (w (i + 1)) : ℕ) : ℝ) / 10000 ≤
      2 * Real.pi := by
    simpa [Nat.cast_sum, Finset.sum_div] using hsumPair
  have hPairReal : ((∑ i, k9PairUnits (w i) (w (i + 1)) : ℕ) : ℝ) ≤ 62832 := by
    linarith [Real.pi_lt_d6]
  have hPairNat : (∑ i, k9PairUnits (w i) (w (i + 1))) ≤ 62832 := by
    exact_mod_cast hPairReal
  rcases k9_six_bin_word_excluded w with hExtra | hPair <;> omega

theorem SelectedPacking15.K9m0_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 9) (hm : (nonOuterIndices p b).card = 0) : False := by
  classical
  have hp := boundary_nonOuter_touching_card_partition p b h.inDisk
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin 6) ≤ (touchingInnerSet p b).card by simp; omega)
  have hd (i : Fin 6) : ‖p (e i)‖ < b ∧ TouchesOuter p b (e i) := by
    have hc := he ⟨i, rfl⟩
    simpa [touchingInnerSet] using hc
  exact h.six_touching_K_ge_nine_impossible (by omega) e e.injective
    (fun i => (hd i).1) (fun i => (hd i).2)

end CP15
