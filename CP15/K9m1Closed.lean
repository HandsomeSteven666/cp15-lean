import CP15.K9m1Tables
import CP15.RemainingCoreBounds

namespace CP15

set_option maxHeartbeats 0

/-- Every actual center, every pairwise directed angle, the wrap bounds,
and the exact integer word domain enter the proved finite-box checker. -/
theorem SelectedPacking15.K9m1_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 9) (hm : (nonOuterIndices p b).card = 1) : False := by
  classical
  obtain ⟨core, hcore⟩ := Finset.card_pos.mp (show 0 < (nonOuterIndices p b).card by omega)
  have hcoreData : ‖p core‖ < b ∧ ¬TouchesOuter p b core := by
    simpa [nonOuterIndices] using hcore
  have hcr := h.K9_core_radius_bounds hK core hcoreData.1 hcoreData.2
  obtain ⟨aBin, haLo, haHi⟩ := k9m1_core_bin_cover ‖p core‖ hcr.1.le hcr.2.le
  have hp := boundary_nonOuter_touching_card_partition p b h.inDisk
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin 5) ≤ (touchingInnerSet p b).card by simp; omega)
  have hd (i : Fin 5) : ‖p (e i)‖ < b ∧ TouchesOuter p b (e i) := by
    have hx := he ⟨i, rfl⟩
    simpa [touchingInnerSet] using hx
  obtain ⟨src, φ, hmono, harg, hrange⟩ := exists_relative_polar_permutation
    (fun i => p (e i)) (polarArg (p core)) (polarArg_range (p core))
  let ix : Fin 5 → Fin 15 := fun i => e (src i)
  have hix : Function.Injective ix := e.injective.comp src.injective
  have hixcore (i : Fin 5) : ix i ≠ core := by
    intro hi
    exact hcoreData.2 (hi ▸ (hd (src i)).2)
  have hb : (323 / 100 : ℝ) < b := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sqrt_nonneg 5, h.elementaryLower]
  have hlo (i : Fin 5) : (123 / 100 : ℝ) ≤ ‖p (ix i)‖ := by
    obtain ⟨j, _, hj, hc⟩ := (hd (src i)).2
    have hn := norm_add_le (p j - p (ix i)) (p (ix i))
    have hdj : ‖p j - p (ix i)‖ = 2 := by simpa [dist_eq_norm, norm_sub_rev] using hc
    rw [sub_add_cancel, hj, hdj] at hn
    linarith
  have hhi (i : Fin 5) : ‖p (ix i)‖ ≤ 4771 / 2000 := by
    have hc := (h.innerCap _ (hd (src i)).1).trans
      (D_lt_shared_high_ceiling b (by linarith) h.belowCandidate)
    linarith
  have hbins (i : Fin 5) := k9m1_touch_bin_cover ‖p (ix i)‖ (hlo i) (hhi i)
  choose w hwLo hwHi using hbins
  have hAY (i : Fin 5) (g : ℝ)
      (hcos : Real.cos (polarArg (p core) - polarArg (p (ix i))) = Real.cos g)
      (hg : 0 ≤ g) : (k9m1AY aBin (w i) : ℝ) / 10000 ≤ g :=
    k9m1_AY_angle_lower (p core) (p (ix i)) g aBin (w i)
      haLo haHi (hwLo i) (hwHi i) (h.separated _ _ (hixcore i).symm) hcos hg
  have hYY (i j : Fin 5) (hij : i ≠ j) (g : ℝ)
      (hcos : Real.cos (polarArg (p (ix i)) - polarArg (p (ix j))) = Real.cos g)
      (hg : 0 ≤ g) : (k9m1YY (w i) (w j) : ℝ) / 10000 ≤ g :=
    k9m1_YY_angle_lower (p (ix i)) (p (ix j)) g (w i) (w j)
      (hwLo i) (hwHi i) (hwLo j) (hwHi j) (h.separated _ _ (hix.ne hij)) hcos hg
  have hangle := mixed_actual_angular_bounds (p core) (fun i => p (ix i)) φ
    hmono harg hrange k9m1AY k9m1YY aBin w hAY hYY
  have hroot : k9m1Root.Contains (mixedBinWord aBin w) := by
    intro i
    fin_cases i
    · change 0 ≤ aBin.val ∧ aBin.val ≤ 10
      have ht := aBin.isLt
      omega
    · change 0 ≤ (w 0).val ∧ (w 0).val ≤ 19
      have ht := (w 0).isLt
      omega
    · change 0 ≤ (w 1).val ∧ (w 1).val ≤ 19
      have ht := (w 1).isLt
      omega
    · change 0 ≤ (w 2).val ∧ (w 2).val ≤ 19
      have ht := (w 2).isLt
      omega
    · change 0 ≤ (w 3).val ∧ (w 3).val ≤ 19
      have ht := (w 3).isLt
      omega
    · change 0 ≤ (w 4).val ∧ (w 4).val ≤ 19
      have ht := (w 4).isLt
      omega
  have hcost := h.touching_cost_budget (by omega) ix hix
    (fun i => (hd (src i)).1) (fun i => (hd (src i)).2)
  have heachExtra (i : Fin 5) : (k9m1Extra (w i) : ℝ) / 10000 ≤
      max 0 (2 * contactAngle b ‖p (ix i)‖ - 57588 / 100000) :=
    k9m1_extra_lower h (ix i) (hd (src i)).1 (hd (src i)).2 (w i) (hwLo i)
  have hsumExtra := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heachExtra i)
  have hsumExtra' : ((∑ i, k9m1Extra (w i) : ℕ) : ℝ) / 10000 ≤
      ∑ i, max 0 (2 * contactAngle b ‖p (ix i)‖ - 57588 / 100000) := by
    simpa [Nat.cast_sum, Finset.sum_div] using hsumExtra
  simp only [hK, Nat.cast_ofNat] at hcost
  have hExtraReal : ((∑ i, k9m1Extra (w i) : ℕ) : ℝ) ≤ 11010 := by
    nlinarith [Real.pi_lt_d6]
  have hExtraNat : (∑ i, k9m1Extra (w i)) ≤ 11010 := by exact_mod_cast hExtraReal
  apply k9m1_discrete_impossible (mixedBinWord aBin w) hroot
    (fun i => 10000 * Fin.cases (polarArg (p core)) φ i)
  · change (∑ i, mixedBinExtra k9m1Extra i (mixedBinWord aBin w i)) ≤ 11010
    rw [mixedBinExtra_sum]
    exact hExtraNat
  · exact hangle

end CP15
