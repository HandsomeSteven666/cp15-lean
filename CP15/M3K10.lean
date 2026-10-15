import CP15.StrongOuterGap
import CP15.M3DistinctBudget
import CP15.M3RadiusCutoff

open scoped InnerProductSpace

namespace CP15

/-- A single high-radius inner center with squared radius above `16/3`
and an actual outer contact overdraws a ten-center outer ring. -/
theorem no_shared_size_outer_contact_at_K10
    (p : Fin 15 → Plane) (b : ℝ)
    (hb3 : 3 < b) (hbB : b ≤ candidateB)
    (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 10 ≤ (boundarySet p b).card)
    (inner outer : Fin 15)
    (hinner : ‖p inner‖ < b)
    (hsq : (16 / 3 : ℝ) < ‖p inner‖ ^ 2)
    (houter : ‖p outer‖ = b)
    (htouch : dist (p inner) (p outer) = 2) : False := by
  classical
  let inn : Fin 1 → Fin 15 := fun _ => inner
  let out : Fin 1 → Fin 15 := fun _ => outer
  have hinj : Function.Injective inn := by
    intro a c _
    fin_cases a
    fin_cases c
    rfl
  have hradius : 2 ≤ ‖p inner‖ := by
    have hn := norm_nonneg (p inner)
    nlinarith
  obtain ⟨charge, offset, hcharge, hdata, hbudget, _⟩ :=
    exists_large_contact_exact_gap_budget p b (by linarith) hbB hsep hD
      (by omega) inn out hinj (fun _ => hinner)
      (fun _ => hradius) (fun _ => houter) (fun _ => htouch)
  have hδ : (5 / 9 : ℝ) < offset 0 :=
    capped_shared_contact_offset_gt_five_ninths b ‖p inner‖ (offset 0)
      hb3 hbB hsq (norm_nonneg _) (hD _ hinner)
      (by linarith [(hdata 0).1]) (hdata 0).2.2
  have hsize : 10 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    exact hK
  have himage : (Finset.univ.image charge).card = 1 := by
    simp
  have hsubset : Finset.univ.image charge ⊆
      (Finset.univ : Finset (Fin (boundaryAngles p b).card)) := by simp
  have hcompcard : 9 ≤ (Finset.univ \ Finset.univ.image charge).card := by
    rw [Finset.card_sdiff_of_subset hsubset, himage]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hother : (207 / 40 : ℝ) ≤
      ∑ _u ∈ Finset.univ \ Finset.univ.image charge, (23 / 40 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcast : (9 : ℝ) ≤
        ((Finset.univ \ Finset.univ.image charge).card : ℝ) := by
      exact_mod_cast hcompcard
    nlinarith
  have hsize2 : 2 ≤ (boundaryAngles p b).card := by omega
  have hstrong : (∑ c : Fin 1, 2 * offset c) +
      (∑ _u ∈ Finset.univ \ Finset.univ.image charge,
        (23 / 40 : ℝ)) ≤ 2 * Real.pi := by
    exact injective_gap_budget Finset.univ charge (fun c => 2 * offset c)
      (nextBoundaryGap p b hsize2) (23 / 40) (2 * Real.pi)
      hcharge (by simp) (fun c => (hdata c).2.1)
      (fun u _ => every_next_gap_ge_23_div_40 p b (by linarith)
        hbB hsep hsize2 u)
      (sum_next_boundary_gaps p b hsize2)
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d20]
  rw [Fin.sum_univ_one] at hstrong
  linarith

/-- The selected-packing `m ≥ 3` case is impossible with ten boundary
centers. The shared blocker is obtained from the complete incidence split;
its squared-radius threshold supplies the strict charged-gap cost. -/
theorem m3_impossible_at_K10
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hFcap : ∀ t, ‖p t‖ < b → ¬TouchesOuter p b t → ‖p t‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ t, ‖p t‖ < b → p t ≠ 0 →
      ∃ j, j ≠ t ∧ dist (p t) (p j) = 2 ∧
        ‖p t‖ ^ 2 < ⟪p j, p t⟫_ℝ)
    (hK : 10 ≤ (boundarySet p b).card)
    (hm3 : 3 ≤ (nonOuterIndices p b).card) : False := by
  classical
  have hbcut := m3_radius_cutoff p b hb hpack hD hblock hFcap
    hFsmall hm3
  have hroot : (3 / 2 : ℝ) < Real.sqrt 3 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hb3 : 3 < b := by linarith
  obtain ⟨target, blocker, htarget, hno, hdata, hpair, _, hshared⟩ :=
    m3_selected_blockers_have_shared_pair p b hb hbB hpack hD hFcap
      hFsmall hblock (by omega) hm3
  have hcontradiction (c d : Fin 3) (hcd : c ≠ d)
      (hsame : blocker c = blocker d) : False := by
    have hsq := hshared c d hcd hsame
    obtain ⟨outer, _, hout, ht⟩ := (hdata c).2.2.1
    exact no_shared_size_outer_contact_at_K10 p b hb3 hbB hpack.2 hD
      hK (blocker c) outer (hdata c).1 hsq hout ht
  rcases hpair with h01 | h02 | h12
  · exact hcontradiction 0 1 (by decide) h01
  · exact hcontradiction 0 2 (by decide) h02
  · exact hcontradiction 1 2 (by decide) h12

end CP15
