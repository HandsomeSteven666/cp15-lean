import CP15.M3Closed
import CP15.M2BlockerBridge

open scoped InnerProductSpace

namespace CP15

/-- Two distinct high-radius inner centers with actual outer contacts
overdraw a ten-point outer ring. The charges are injective; every one of
the other eight gaps pays the checked `23/40` baseline. -/
theorem no_two_distinct_large_outer_contacts_at_K10
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 10 ≤ (boundarySet p b).card)
    (inner outer : Fin 2 → Fin 15)
    (hinj : Function.Injective inner)
    (hinner : ∀ c, ‖p (inner c)‖ < b)
    (hradius : ∀ c, 2 ≤ ‖p (inner c)‖)
    (houter : ∀ c, ‖p (outer c)‖ = b)
    (htouch : ∀ c, dist (p (inner c)) (p (outer c)) = 2) : False := by
  classical
  obtain ⟨charge, offset, hcharge, hdata, _, _⟩ :=
    exists_large_contact_exact_gap_budget p b hb hbB hsep hD
      (by omega) inner outer hinj hinner hradius houter htouch
  have hδ (c : Fin 2) : (12 / 25 : ℝ) < offset c :=
    capped_large_contact_offset_gt_twelve_twentyfifths b
      ‖p (inner c)‖ (offset c) hb hbB (hradius c)
      (hD _ (hinner c)) (by linarith [(hdata c).1])
      (hdata c).2.2
  have hsize : 10 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    exact hK
  have himage : (Finset.univ.image charge).card = 2 := by
    simp [Finset.card_image_of_injective _ hcharge]
  have hsubset : Finset.univ.image charge ⊆
      (Finset.univ : Finset (Fin (boundaryAngles p b).card)) := by simp
  have hcompcard : 8 ≤ (Finset.univ \ Finset.univ.image charge).card := by
    rw [Finset.card_sdiff_of_subset hsubset, himage]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hother : (23 / 5 : ℝ) ≤
      ∑ _u ∈ Finset.univ \ Finset.univ.image charge,
        (23 / 40 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcast : (8 : ℝ) ≤
        ((Finset.univ \ Finset.univ.image charge).card : ℝ) := by
      exact_mod_cast hcompcard
    nlinarith
  have hsize2 : 2 ≤ (boundaryAngles p b).card := by omega
  have hstrong : (∑ c : Fin 2, 2 * offset c) +
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
  rw [Fin.sum_univ_two] at hstrong
  linarith [hδ 0, hδ 1]

/-- Extract both selected strict blockers and their actual outer contacts
from a cardinal `m ≥ 2` hypothesis. The two blocker labels may coincide. -/
theorem m2_selected_blockers
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hpack : InDisk b p ∧ Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hFcap : ∀ t, ‖p t‖ < b → ¬TouchesOuter p b t → ‖p t‖ ≤ F b)
    (hFsmall : F b < Real.sqrt 2)
    (hblock : ∀ t, ‖p t‖ < b → p t ≠ 0 →
      ∃ j, j ≠ t ∧ dist (p t) (p j) = 2 ∧
        ‖p t‖ ^ 2 < ⟪p j, p t⟫_ℝ)
    (hK : 9 ≤ (boundarySet p b).card)
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
          ⟪p (blocker c), p (target c)⟫_ℝ) := by
  classical
  have htwo : Fintype.card (Fin 2) ≤
      (nonOuterIndices p b).card := by simpa using hm2
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset htwo
  have hno (c : Fin 2) : ‖p (e c)‖ < b ∧
      ¬TouchesOuter p b (e c) := by
    have hc : e c ∈ nonOuterIndices p b := he ⟨c, rfl⟩
    simpa [nonOuterIndices] using hc
  have hnz := nonOuter_pair_nonzero p b hpack.2 hFcap hFsmall
    (e 0) (e 1) (e.injective.ne (by decide)) (hno 0) (hno 1)
  have hnonzero (c : Fin 2) : p (e c) ≠ 0 := by
    fin_cases c
    · exact hnz.1
    · exact hnz.2
  obtain ⟨blocker, outer, hdata, _⟩ :=
    exists_nonOuter_blocker_family_with_conditional_budget p b hb hbB
      hpack hD hFcap hFsmall hblock hK e
      (fun c => ⟨(hno c).1, (hno c).2, hnonzero c⟩)
  exact ⟨e, blocker, outer, e.injective, hno, hdata⟩

/-- Both `m = 2` incidence patterns are impossible at `K = 10`.
The shared case uses the strict contact capacity bound `s² > 16/3`;
the distinct case uses two injective gap charges. -/
theorem m2_impossible_at_K10
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
    (hm2 : 2 ≤ (nonOuterIndices p b).card) : False := by
  classical
  obtain ⟨target, blocker, outer, htarget, _, hdata⟩ :=
    m2_selected_blockers p b hb hbB hpack hD hFcap hFsmall hblock
      (by omega) hm2
  by_cases hsame : blocker 0 = blocker 1
  · have hsq : (16 / 3 : ℝ) < ‖p (blocker 0)‖ ^ 2 :=
      selected_shared_blocker_sq_gt_sixteen_thirds p hpack.2
        target blocker htarget
        (fun c => (hdata c).2.1)
        (fun c => (hdata c).2.2.2.2.2.2.2)
        0 1 (by decide) hsame
    have hroot : (3 / 2 : ℝ) < Real.sqrt 3 := by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      have hn := Real.sqrt_nonneg (3 : ℝ)
      nlinarith
    have hb3 : 3 < b := by
      have hDgt : (16 / 3 : ℝ) < D b ^ 2 := by
        have hd := hD (blocker 0) (hdata 0).2.2.1
        have hn := norm_nonneg (p (blocker 0))
        nlinarith
      have hrad : 0 ≤ D b ^ 2 - 4 := by linarith
      have hFsq : F b ^ 2 = D b ^ 2 - 4 := by
        unfold F
        exact Real.sq_sqrt hrad
      have hbcut := radius_gt_two_sqrt_three_of_F_sq b hb (by linarith)
      linarith
    exact no_shared_size_outer_contact_at_K10 p b hb3 hbB hpack.2
      hD hK (blocker 0) (outer 0)
      (hdata 0).2.2.1 hsq
      (hdata 0).2.2.2.2.2.1
      (hdata 0).2.2.2.2.2.2.1
  · have hinj : Function.Injective blocker := by
      intro c d h
      fin_cases c <;> fin_cases d <;> simp_all
    exact no_two_distinct_large_outer_contacts_at_K10 p b hb hbB
      hpack.2 hD hK blocker outer hinj
      (fun c => (hdata c).2.2.1)
      (fun c => (hdata c).2.2.2.1.le)
      (fun c => (hdata c).2.2.2.2.2.1)
      (fun c => (hdata c).2.2.2.2.2.2.1)

end CP15
