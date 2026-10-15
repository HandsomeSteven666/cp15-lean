import CP15.M2K9Geometry
import CP15.K9ScalarBounds

namespace CP15

/-- Three distinct radius-at-least-two inner centers touching the outer
ring cannot coexist with nine boundary centers. The proof uses the
already checked injective outer-gap assignment and a new exact rational
cosine corner at `12/25` radians. -/
theorem k9_three_high_touching_inner_impossible
    (p : Fin 15 → Plane) (b : ℝ)
    (hb3 : 3 < b) (hbB : b ≤ candidateB)
    (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK9 : (boundarySet p b).card = 9)
    (inner outer : Fin 3 → Fin 15)
    (hinj : Function.Injective inner)
    (hinner : ∀ c, ‖p (inner c)‖ < b)
    (hradius : ∀ c, 2 ≤ ‖p (inner c)‖)
    (houter : ∀ c, ‖p (outer c)‖ = b)
    (htouch : ∀ c, dist (p (inner c)) (p (outer c)) = 2) :
    False := by
  classical
  obtain ⟨charge, offset, hcharge, hoffset, hbudget, _⟩ :=
    exists_large_contact_exact_gap_budget p b (by linarith) hbB
      hsep hD (by omega) inner outer hinj hinner hradius houter htouch
  have hBq : b ≤ (352136 / 100000 : ℝ) :=
    (hbB.trans_lt Candidate.candidateB_lt_352136_div_100000).le
  have hδ (c : Fin 3) : (12 / 25 : ℝ) < offset c := by
    have hsupper : ‖p (inner c)‖ ≤ 12 / 5 :=
      ((hD (inner c) (hinner c)).trans
        (D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB)).le
    have hsize : 9 ≤ (boundaryAngles p b).card := by
      rw [boundaryAngles_card p b hsep, hK9]
    have hδpi : offset c ≤ Real.pi := by
      have hgap := every_next_gap_lt_pi p b (by linarith) hbB
        hsep (by omega) (charge c)
      have hle := (hoffset c).2.1
      have hpos := (hoffset c).1
      linarith
    exact contact_offset_gt_rational_angle b (352136 / 100000)
      2 ‖p (inner c)‖ (offset c) (12 / 25)
      hb3 hBq (by norm_num) (by norm_num) (hradius c) hsupper
      (by linarith [(hoffset c).1]) hδpi
      (by norm_num) (by norm_num)
      (by norm_num [contactCos, sinCubicUpper])
      (hoffset c).2.2
  have himage : (Finset.univ.image charge).card = 3 := by
    simp [Finset.card_image_of_injective _ hcharge]
  have hsubset : Finset.univ.image charge ⊆
      (Finset.univ : Finset (Fin (boundaryAngles p b).card)) := by simp
  have hcompcard :
      (Finset.univ \ Finset.univ.image charge).card = 6 := by
    rw [Finset.card_sdiff_of_subset hsubset, himage]
    simp [boundaryAngles_card p b hsep, hK9]
  rw [Fin.sum_univ_three] at hbudget
  simp only [Finset.sum_const, nsmul_eq_mul, hcompcard] at hbudget
  have hpi : Real.pi < (3141593 / 1000000 : ℝ) := by
    linarith [Real.pi_lt_d6]
  have hδ0 := hδ 0
  have hδ1 := hδ 1
  have hδ2 := hδ 2
  norm_num at hbudget ⊢
  linarith

/-- At most two of the four touching inner centers can have radius
strictly above two. This includes all choices of an outer contact. -/
theorem k9_high_touching_inner_count_le_two
    (p : Fin 15 → Plane) (b : ℝ)
    (hb3 : 3 < b) (hbB : b ≤ candidateB)
    (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK9 : (boundarySet p b).card = 9) :
    ((touchingInnerSet p b).filter
      (fun i => 2 < ‖p i‖)).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree : Fintype.card (Fin 3) ≤
      ((touchingInnerSet p b).filter
        (fun i => 2 < ‖p i‖)).card := by
    simp
    omega
  obtain ⟨inner, hmem⟩ :=
    Function.Embedding.exists_of_card_le_finset hthree
  have hdata (c : Fin 3) :
      ‖p (inner c)‖ < b ∧ 2 ≤ ‖p (inner c)‖ ∧
        TouchesOuter p b (inner c) := by
    have hc := hmem ⟨c, rfl⟩
    have hc' : inner c ∈ touchingInnerSet p b ∧
        2 < ‖p (inner c)‖ := by
      simpa using hc
    have ht : ‖p (inner c)‖ < b ∧
        TouchesOuter p b (inner c) := by
      simpa [touchingInnerSet] using hc'.1
    exact ⟨ht.1, hc'.2.le, ht.2⟩
  let outer : Fin 3 → Fin 15 :=
    fun c => Classical.choose (hdata c).2.2
  have houter (c : Fin 3) : ‖p (outer c)‖ = b :=
    (Classical.choose_spec (hdata c).2.2).2.1
  have htouch (c : Fin 3) :
      dist (p (inner c)) (p (outer c)) = 2 :=
    (Classical.choose_spec (hdata c).2.2).2.2
  exact k9_three_high_touching_inner_impossible p b hb3 hbB hsep
    hD hK9 inner outer inner.injective (fun c => (hdata c).1)
    (fun c => (hdata c).2.1) houter htouch

end CP15
