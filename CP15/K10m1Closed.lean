import CP15.K10m1Tables
import CP15.RelativePolarOrder

namespace CP15

set_option maxHeartbeats 0

/-- The actual core and all four touching centers are placed in a full
turn starting at the core. Equal polar arguments give zero gaps and are
retained. Every bin and every budget in the finite checker is thus a
necessary condition on the original selected packing. -/
theorem SelectedPacking15.K10m1_impossible
    {p : Fin 15 → Plane} {b : ℝ} (h : SelectedPacking15 p b)
    (hK : (boundarySet p b).card = 10) (hm : (nonOuterIndices p b).card = 1) : False := by
  classical
  obtain ⟨core, hcore⟩ := Finset.card_pos.mp (show 0 < (nonOuterIndices p b).card by omega)
  have hcoreData : ‖p core‖ < b ∧ ¬TouchesOuter p b core := by
    simpa [nonOuterIndices] using hcore
  have hcr := h.K10_core_radius_bounds hK core hcoreData.1 hcoreData.2
  obtain ⟨aBin, haLo, haHi⟩ := k10_core_bin_cover ‖p core‖ hcr.1.le hcr.2.le
  have hp := boundary_nonOuter_touching_card_partition p b h.inDisk
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin 4) ≤ (touchingInnerSet p b).card by simp; omega)
  have hd (i : Fin 4) : ‖p (e i)‖ < b ∧ TouchesOuter p b (e i) := by
    have hx := he ⟨i, rfl⟩
    simpa [touchingInnerSet] using hx
  obtain ⟨src, φ, hmono, harg, hrange⟩ := exists_relative_polar_permutation
    (fun i => p (e i)) (polarArg (p core)) (polarArg_range (p core))
  let ix : Fin 4 → Fin 15 := fun i => e (src i)
  have hix : Function.Injective ix := e.injective.comp src.injective
  have hixcore (i : Fin 4) : ix i ≠ core := by
    intro hi
    exact hcoreData.2 (hi ▸ (hd (src i)).2)
  have hb : (323 / 100 : ℝ) < b := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sqrt_nonneg 5, h.elementaryLower]
  have hlo (i : Fin 4) : (123 / 100 : ℝ) ≤ ‖p (ix i)‖ := by
    obtain ⟨j, _, hj, hc⟩ := (hd (src i)).2
    have hn := norm_add_le (p j - p (ix i)) (p (ix i))
    have hdj : ‖p j - p (ix i)‖ = 2 := by simpa [dist_eq_norm, norm_sub_rev] using hc
    rw [sub_add_cancel, hj, hdj] at hn
    linarith
  have hhi (i : Fin 4) : ‖p (ix i)‖ ≤ 4771 / 2000 := by
    have hc := (h.innerCap _ (hd (src i)).1).trans
      (D_lt_shared_high_ceiling b (by linarith) h.belowCandidate)
    linarith
  have hbins (i : Fin 4) := k10_touch_bin_cover ‖p (ix i)‖ (hlo i) (hhi i)
  choose w hwLo hwHi using hbins
  let g : Fin 5 → ℝ := ![φ 0 - polarArg (p core), φ 1 - φ 0,
    φ 2 - φ 1, φ 3 - φ 2, polarArg (p core) + 2 * Real.pi - φ 3]
  have hgap (i : Fin 5) : 0 ≤ g i := by
    have h01 := hmono (show (0 : Fin 4) ≤ 1 by decide)
    have h12 := hmono (show (1 : Fin 4) ≤ 2 by decide)
    have h23 := hmono (show (2 : Fin 4) ≤ 3 by decide)
    fin_cases i <;> norm_num [g] <;> linarith [(hrange 0).1, (hrange 3).2]
  have hsumg : (∑ i, g i) = 2 * Real.pi := by
    norm_num [g, Fin.sum_univ_succ]
  have hAYcos (i : Fin 4) :
      Real.cos (polarArg (p core) - polarArg (p (ix i))) =
        Real.cos (φ i - polarArg (p core)) := by
    rw [polarLiftFrom_cos (polarArg (p core)), polarLiftFrom_self, harg i]
    rw [← Real.cos_neg (polarArg (p core) - φ i)]
    congr 1
    ring
  have hYYcos (i j : Fin 4) :
      Real.cos (polarArg (p (ix i)) - polarArg (p (ix j))) = Real.cos (φ j - φ i) := by
    rw [polarLiftFrom_cos (polarArg (p core)), harg i, harg j]
    rw [← Real.cos_neg (φ i - φ j)]
    congr 1
    ring
  have hlastCos : Real.cos (polarArg (p core) - polarArg (p (ix 3))) = Real.cos (g 4) := by
    rw [hAYcos 3]
    change Real.cos (φ 3 - polarArg (p core)) =
      Real.cos (polarArg (p core) + 2 * Real.pi - φ 3)
    rw [show polarArg (p core) + 2 * Real.pi - φ 3 =
      (polarArg (p core) - φ 3) + 2 * Real.pi by ring, Real.cos_add_two_pi]
    rw [← Real.cos_neg (φ 3 - polarArg (p core))]
    congr 1
    ring
  let angles : Fin 5 → ℕ := ![k10AYUnits aBin (w 0), k10YYUnits (w 0) (w 1),
    k10YYUnits (w 1) (w 2), k10YYUnits (w 2) (w 3), k10AYUnits aBin (w 3)]
  have hpair (i : Fin 5) : (angles i : ℝ) / 10000 ≤ g i := by
    fin_cases i
    · exact k10_AY_angle_lower (p core) (p (ix 0)) (g 0) aBin (w 0)
        haLo haHi (hwLo 0) (hwHi 0) (h.separated _ _ (hixcore 0).symm) (hAYcos 0) (hgap 0)
    · exact k10_YY_angle_lower (p (ix 0)) (p (ix 1)) (g 1) (w 0) (w 1)
        (hwLo 0) (hwHi 0) (hwLo 1) (hwHi 1)
        (h.separated _ _ (hix.ne (by decide))) (hYYcos 0 1) (hgap 1)
    · exact k10_YY_angle_lower (p (ix 1)) (p (ix 2)) (g 2) (w 1) (w 2)
        (hwLo 1) (hwHi 1) (hwLo 2) (hwHi 2)
        (h.separated _ _ (hix.ne (by decide))) (hYYcos 1 2) (hgap 2)
    · exact k10_YY_angle_lower (p (ix 2)) (p (ix 3)) (g 3) (w 2) (w 3)
        (hwLo 2) (hwHi 2) (hwLo 3) (hwHi 3)
        (h.separated _ _ (hix.ne (by decide))) (hYYcos 2 3) (hgap 3)
    · exact k10_AY_angle_lower (p core) (p (ix 3)) (g 4) aBin (w 3)
        haLo haHi (hwLo 3) (hwHi 3) (h.separated _ _ (hixcore 3).symm) hlastCos (hgap 4)
  have hsumPair := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpair i)
  rw [hsumg] at hsumPair
  have hPairReal : ((k10AYUnits aBin (w 0) + k10YYUnits (w 0) (w 1) +
      k10YYUnits (w 1) (w 2) + k10YYUnits (w 2) (w 3) + k10AYUnits aBin (w 3) : ℕ) : ℝ) ≤ 62832 := by
    norm_num [angles, Fin.sum_univ_succ, Nat.cast_add] at hsumPair ⊢
    linarith [Real.pi_lt_d6]
  have hPairNat : k10AYUnits aBin (w 0) + k10YYUnits (w 0) (w 1) +
      k10YYUnits (w 1) (w 2) + k10YYUnits (w 2) (w 3) + k10AYUnits aBin (w 3) ≤ 62832 := by
    exact_mod_cast hPairReal
  have hcost := h.touching_cost_budget (by omega) ix hix
    (fun i => (hd (src i)).1) (fun i => (hd (src i)).2)
  have heachExtra (i : Fin 4) : (k10ExtraUnits (w i) : ℝ) / 10000 ≤
      max 0 (2 * contactAngle b ‖p (ix i)‖ - 57588 / 100000) :=
    k10_touch_bin_extra_lower h (ix i) (hd (src i)).1 (hd (src i)).2 (w i) (hwLo i)
  have hsumExtra := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heachExtra i)
  have hsumExtra' : ((∑ i, k10ExtraUnits (w i) : ℕ) : ℝ) / 10000 ≤
      ∑ i, max 0 (2 * contactAngle b ‖p (ix i)‖ - 57588 / 100000) := by
    simpa [Nat.cast_sum, Finset.sum_div] using hsumExtra
  simp only [hK, Nat.cast_ofNat] at hcost
  have hExtraReal : ((∑ i, k10ExtraUnits (w i) : ℕ) : ℝ) ≤ 5252 := by
    nlinarith [Real.pi_lt_d6]
  have hExtraNat : (∑ i, k10ExtraUnits (w i)) ≤ 5252 := by exact_mod_cast hExtraReal
  rcases k10_four_bin_word_excluded aBin w with hExtra | hPair <;> omega

end CP15
