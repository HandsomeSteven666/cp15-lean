import CP15.CollisionBudget

open scoped InnerProductSpace

namespace CP15

theorem D_lt_twelve_fifths_of_le_candidateB (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) : D b < 12 / 5 := by
  have hrec : 4 / candidateB ≤ 4 / b := by
    apply (div_le_div_iff₀ candidateB_pos hb).2
    nlinarith
  have hDB := Candidate.D_candidateB_lt_12_div_5
  unfold D at hDB ⊢
  linarith

theorem cos_diff_of_two_pi_lifts (x y : Plane) (θx θy : ℝ)
    (hx : θx = polarArg x ∨ θx = polarArg x + 2 * Real.pi)
    (hy : θy = polarArg y ∨ θy = polarArg y + 2 * Real.pi) :
    Real.cos (polarArg x - polarArg y) = Real.cos (θx - θy) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rw [hx, hy]
  · rw [hx, hy, cos_sub_add_two_pi_right]
  · rw [hx, hy, cos_add_two_pi_sub_left]
  · rw [hx, hy]
    have h : (polarArg x + 2 * Real.pi) - (polarArg y + 2 * Real.pi) =
        polarArg x - polarArg y := by ring
    rw [h]

theorem next_gap_right_succ (p : Fin 15 → Plane) (b : ℝ)
    (hsize : 2 ≤ (boundaryAngles p b).card)
    (u : Fin (boundaryAngles p b).card)
    (hu : u.val + 1 < (boundaryAngles p b).card) :
    (boundaryAngles p b).orderEmbOfFin rfl u +
      nextBoundaryGap p b hsize u =
        (boundaryAngles p b).orderEmbOfFin rfl ⟨u.val + 1, hu⟩ := by
  simp [nextBoundaryGap, hu]

theorem next_gap_right_last (p : Fin 15 → Plane) (b : ℝ)
    (hsize : 2 ≤ (boundaryAngles p b).card) :
    (boundaryAngles p b).orderEmbOfFin rfl
        ⟨(boundaryAngles p b).card - 1, by omega⟩ +
      nextBoundaryGap p b hsize
        ⟨(boundaryAngles p b).card - 1, by omega⟩ =
      (boundaryAngles p b).orderEmbOfFin rfl ⟨0, by omega⟩ +
        2 * Real.pi := by
  have hnot : ¬ (boundaryAngles p b).card - 1 + 1 <
      (boundaryAngles p b).card := by omega
  simp [nextBoundaryGap, hnot]

/-- A separated pair with radii between `2` and `12/5` cannot have a
circular angular separation at most `4/5`. The real lifts are explicit, so
the lemma applies equally to an ordinary gap and the closing wrap gap. -/
theorem large_inner_pair_angle_gt_four_fifths (x y : Plane) (θx θy : ℝ)
    (hxlo : 2 ≤ ‖x‖) (hxhi : ‖x‖ ≤ 12 / 5)
    (hylo : 2 ≤ ‖y‖) (hyhi : ‖y‖ ≤ 12 / 5)
    (hsep : 2 ≤ dist x y)
    (hlift : Real.cos (polarArg x - polarArg y) =
      Real.cos (θx - θy)) :
    (4 / 5 : ℝ) < |θx - θy| := by
  by_contra hnot
  have habs : |θx - θy| ≤ (4 / 5 : ℝ) := le_of_not_gt hnot
  have hθlo : -(4 / 5 : ℝ) ≤ θx - θy := by
    have := (abs_le.mp habs).1
    linarith
  have hθhi : θx - θy ≤ (4 / 5 : ℝ) := (abs_le.mp habs).2
  have hsq : (θx - θy) ^ 2 ≤ (4 / 5 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (θx - θy + 4 / 5),
      sq_nonneg (4 / 5 - (θx - θy))]
  have hcosbound : (17 / 25 : ℝ) ≤ Real.cos (θx - θy) := by
    have hTaylor := Real.one_sub_sq_div_two_le_cos (x := θx - θy)
    nlinarith
  let a := ‖x‖ - 2
  let c := ‖y‖ - 2
  have ha : 0 ≤ a ∧ a ≤ 2 / 5 := by dsimp [a]; constructor <;> linarith
  have hc : 0 ≤ c ∧ c ≤ 2 / 5 := by dsimp [c]; constructor <;> linarith
  have haa : 0 ≤ a * (2 / 5 - a) := mul_nonneg ha.1 (by linarith [ha.2])
  have hcc : 0 ≤ c * (2 / 5 - c) := mul_nonneg hc.1 (by linarith [hc.2])
  have hac : 0 ≤ a * c := mul_nonneg ha.1 hc.1
  have hpoly : ‖x‖ ^ 2 + ‖y‖ ^ 2 -
      (34 / 25 : ℝ) * ‖x‖ * ‖y‖ < 4 := by
    dsimp [a, c] at haa hcc hac ha hc
    nlinarith
  have hdist : dist x y ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 -
      2 * ‖x‖ * ‖y‖ * Real.cos (θx - θy) := by
    rw [dist_eq_norm, norm_sub_sq_real, polar_inner, hlift]
    ring
  have hcosprod : 0 ≤ ‖x‖ * ‖y‖ *
      (Real.cos (θx - θy) - 17 / 25) :=
    mul_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg y))
      (by linarith)
  have hdistlt : dist x y ^ 2 < 4 := by
    nlinarith [hpoly, hcosprod, hdist]
  have hdistge : 0 ≤ dist x y := dist_nonneg
  nlinarith

/-- With at least nine boundary centers, the eight *other* gaps each use
at least `4/7` of the angular budget. This bound also applies to the wrap
gap because the omitted index is arbitrary. -/
theorem every_next_gap_lt_twelve_sevenths (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 9 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card) :
    nextBoundaryGap p b
      (by rw [boundaryAngles_card p b hsep]; omega) u < 12 / 7 := by
  let hsize : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  have hother : ((Finset.univ.erase u).card : ℝ) * (4 / 7 : ℝ) ≤
      ∑ v ∈ Finset.univ.erase u, nextBoundaryGap p b hsize v := by
    have hsum := Finset.sum_le_sum (s := Finset.univ.erase u)
      (fun v _ => every_next_gap_ge_four_sevenths p b hb hbB hsep hsize v)
    simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
  have hcard : (Finset.univ.erase u).card =
      (boundaryAngles p b).card - 1 := by
    simp
  have hK' : 9 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    exact hK
  have hcast : (8 : ℝ) ≤ ((boundaryAngles p b).card - 1 : ℕ) := by
    exact_mod_cast (by omega : 8 ≤ (boundaryAngles p b).card - 1)
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d20]
  have htotal := sum_next_boundary_gaps p b hsize
  rw [← Finset.add_sum_erase Finset.univ
    (nextBoundaryGap p b hsize) (Finset.mem_univ u)] at htotal
  rw [hcard] at hother
  nlinarith

/-- A radius-at-least-two inner contact has offset greater than `47/100`.
The proof uses only the exact cosine law, the radial cap, the rational
candidate enclosure, and the global cosine Taylor lower bound. -/
theorem radius_two_contact_offset_gt_47_100 (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hs : 2 ≤ ‖p i‖)
    (hj : ‖p j‖ = b) (hcontact : dist (p i) (p j) = 2) :
    ∃ (v : Fin (boundaryAngles p b).card) (δ : ℝ),
      (47 / 100 : ℝ) < δ ∧
      2 * δ ≤ nextBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) v := by
  obtain ⟨v, δ, hδ0, _, hgap, hcos⟩ :=
    outer_contact_radius_two_cos_support p b hb hbB hsep hD hK
      i j hi hs hj hcontact
  have hbq : b < (353 / 100 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_353_div_100
  have hδlarge : (47 / 100 : ℝ) < δ := by
    by_contra hnot
    have hδhi : δ ≤ (47 / 100 : ℝ) := le_of_not_gt hnot
    have hsq : δ ^ 2 ≤ (47 / 100 : ℝ) ^ 2 := by nlinarith
    have hTaylor := Real.one_sub_sq_div_two_le_cos (x := δ)
    nlinarith
  exact ⟨v, δ, hδlarge, hgap⟩

/-- The radial cap places every radius-at-least-two contact within `π/4`
of its contacted outer direction. This upper bound is useful for detecting
same-side collisions. -/
theorem capped_large_contact_offset_lt_pi_div_four (b s δ : ℝ)
    (hb : 2 < b) (hs : 2 ≤ s) (hsD : s < D b)
    (hδ0 : 0 ≤ δ) (hδhalf : δ < Real.pi / 2)
    (hlaw : 2 * s * b * Real.cos δ = b ^ 2 + s ^ 2 - 4) :
    δ < Real.pi / 4 := by
  have hDb : 2 < D b := lt_of_le_of_lt hs hsD
  have hb3 : 3 < b := by
    unfold D at hDb
    have hmul := mul_lt_mul_of_pos_right hDb (by linarith : 0 < b)
    have hdiv : 4 / b * b = 4 := by field_simp [ne_of_gt (by linarith : 0 < b)]
    rw [sub_mul, hdiv] at hmul
    by_contra hnot
    have hb3' : b ≤ 3 := le_of_not_gt hnot
    nlinarith
  have halign := contact_alignment_strict b s (by linarith) hsD
  have halign' : b ^ 2 - 2 < b ^ 2 * Real.cos δ := by
    have hrel : 2 * s * (b ^ 2 - 2) <
        2 * s * (b ^ 2 * Real.cos δ) := by
      nlinarith [halign, hlaw]
    exact (mul_lt_mul_iff_of_pos_left (by positivity : 0 < 2 * s)).mp hrel
  have hcos : (7 / 9 : ℝ) < Real.cos δ := by
    by_contra hnot
    have hcoshi : Real.cos δ ≤ (7 / 9 : ℝ) := le_of_not_gt hnot
    have hmult : 0 ≤ b ^ 2 * (7 / 9 - Real.cos δ) :=
      mul_nonneg (sq_nonneg b) (by linarith)
    nlinarith [halign']
  have hsqrt : Real.sqrt 2 / 2 < (7 / 9 : ℝ) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  by_contra hnot
  have hδbig : Real.pi / 4 ≤ δ := le_of_not_gt hnot
  have hcos' : Real.cos δ ≤ Real.cos (Real.pi / 4) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity) (by linarith [Real.pi_pos]) hδbig
  rw [Real.cos_pi_div_four] at hcos'
  linarith

theorem actual_large_contact_offset_bounds (q z : Plane) (b δ : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hqlo : 2 ≤ ‖q‖) (hqD : ‖q‖ < D b)
    (hz : ‖z‖ = b) (hcontact : dist q z = 2)
    (hδ0 : 0 ≤ δ) (hδhalf : δ < Real.pi / 2)
    (hcos : Real.cos δ =
      Real.cos (polarArg q - polarArg z)) :
    (47 / 100 : ℝ) < δ ∧ δ < Real.pi / 4 := by
  have hlaw : 2 * ‖q‖ * b * Real.cos δ =
      b ^ 2 + ‖q‖ ^ 2 - 4 := by
    have h := contact_inner_formula q z b ‖q‖ rfl hz hcontact
    rw [polar_inner, hz, ← hcos] at h
    nlinarith
  have hδhi := capped_large_contact_offset_lt_pi_div_four b ‖q‖ δ
    hb hqlo hqD hδ0 hδhalf hlaw
  have hcosbound := contact_offset_cos_le_b_div_four b ‖q‖ δ
    hb hqlo hqD hlaw
  have hbq : b < (353 / 100 : ℝ) :=
    hbB.trans_lt Candidate.candidateB_lt_353_div_100
  have hδlo : (47 / 100 : ℝ) < δ := by
    by_contra hnot
    have hδbound : δ ≤ (47 / 100 : ℝ) := le_of_not_gt hnot
    have hsq : δ ^ 2 ≤ (47 / 100 : ℝ) ^ 2 := by nlinarith
    have hTaylor := Real.one_sub_sq_div_two_le_cos (x := δ)
    nlinarith
  exact ⟨hδlo, hδhi⟩

/-- An actual inner–outer contact has a lifted polar position in one of the
two half-gaps adjoining its outer endpoint. The four cases are ordinary
forward/backward and the two branch-cut orientations. -/
theorem actual_contact_local_gap_position (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hcontact : dist (p i) (p j) = 2) :
    ∃ (v : Fin (boundaryAngles p b).card) (θ δ : ℝ),
      (θ = polarArg (p i) ∨ θ = polarArg (p i) + 2 * Real.pi) ∧
      0 ≤ δ ∧
      2 * δ ≤ nextBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) v ∧
      (θ = (boundaryAngles p b).orderEmbOfFin rfl v + δ ∨
       θ = (boundaryAngles p b).orderEmbOfFin rfl v +
         nextBoundaryGap p b
           (by rw [boundaryAngles_card p b hsep]; omega) v - δ) ∧
      Real.cos δ = Real.cos (polarArg (p i) - polarArg (p j)) := by
  let hsize : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  let e := (boundaryAngles p b).orderEmbOfFin rfl
  obtain ⟨u, hu, hforward | hbackward | hplus | hminus⟩ :=
    every_outer_contact_charges_adjacent_gap p b hb hbB hsep hD hK
      i j hi hj hcontact
  · refine ⟨u, polarArg (p i), polarArg (p i) - polarArg (p j),
      Or.inl rfl, by linarith [hforward.1], hforward.2,
      Or.inl (by linarith), ?_⟩
    rfl
  · by_cases hpositive : 0 < u.val
    · have hv : u.val - 1 < (boundaryAngles p b).card := by
        have := u.isLt
        omega
      let v : Fin (boundaryAngles p b).card := ⟨u.val - 1, hv⟩
      have hsucc : v.val + 1 < (boundaryAngles p b).card := by
        dsimp [v]
        omega
      have hindex : (⟨v.val + 1, hsucc⟩ :
          Fin (boundaryAngles p b).card) = u := by
        apply Fin.ext
        dsimp [v]
        omega
      have hright := next_gap_right_succ p b hsize v hsucc
      rw [hindex] at hright
      have hprev := next_gap_eq_previous_succ p b hsize v hsucc
      rw [hindex] at hprev
      refine ⟨v, polarArg (p i), polarArg (p j) - polarArg (p i),
        Or.inl rfl, by linarith [hbackward.1], ?_, Or.inr ?_, ?_⟩
      · rw [hprev]
        exact hbackward.2
      · linarith [hu, hright]
      · have hneg : polarArg (p j) - polarArg (p i) =
            -(polarArg (p i) - polarArg (p j)) := by ring
        rw [hneg, Real.cos_neg]
    · have hzero : u.val = 0 := by omega
      have hfirst : u = (⟨0, by omega⟩ : Fin (boundaryAngles p b).card) :=
        Fin.ext hzero
      let v : Fin (boundaryAngles p b).card :=
        ⟨(boundaryAngles p b).card - 1, by omega⟩
      have hright := next_gap_right_last p b hsize
      have hprev := next_last_eq_previous_first p b hsize
      refine ⟨v, polarArg (p i) + 2 * Real.pi,
        polarArg (p j) - polarArg (p i), Or.inr rfl,
        by linarith [hbackward.1], ?_, Or.inr ?_, ?_⟩
      · rw [hfirst] at hbackward
        rw [hprev]
        exact hbackward.2
      · rw [hfirst] at hu
        linarith [hu, hright]
      · have hneg : polarArg (p j) - polarArg (p i) =
            -(polarArg (p i) - polarArg (p j)) := by ring
        rw [hneg, Real.cos_neg]
  · refine ⟨u, polarArg (p i) + 2 * Real.pi,
      polarArg (p i) + 2 * Real.pi - polarArg (p j), Or.inr rfl,
      by linarith [hplus.1], hplus.2,
      Or.inl (by linarith), ?_⟩
    rw [cos_add_two_pi_sub_left]
  · have hδpos : 0 < polarArg (p j) + 2 * Real.pi - polarArg (p i) := by
      linarith [hminus.1]
    obtain ⟨v', hv'⟩ := previous_gap_has_next_index p b hsize u
    have hgaplt := every_next_gap_lt_pi p b (by linarith) hbB hsep hK v'
    have hδhalf : polarArg (p j) + 2 * Real.pi - polarArg (p i) <
        Real.pi / 2 := by
      rw [← hv'] at hgaplt
      linarith [hminus.2]
    have hshift : |(polarArg (p i) - 2 * Real.pi) - polarArg (p j)| <
        Real.pi / 2 := by
      have heq : (polarArg (p i) - 2 * Real.pi) - polarArg (p j) =
          -(polarArg (p j) + 2 * Real.pi - polarArg (p i)) := by ring
      rw [heq, abs_neg, abs_of_pos hδpos]
      exact hδhalf
    have hfirstIndex :=
      (backward_shifted_contact_charges_wrap_gap p b hb hbB hsep hD hK
        u i j hi hj hu.symm hcontact hshift).1
    have hzero : u.val = 0 := by omega
    have hfirst : u = (⟨0, by omega⟩ : Fin (boundaryAngles p b).card) :=
      Fin.ext hzero
    let v : Fin (boundaryAngles p b).card :=
      ⟨(boundaryAngles p b).card - 1, by omega⟩
    have hright := next_gap_right_last p b hsize
    have hprev := next_last_eq_previous_first p b hsize
    refine ⟨v, polarArg (p i),
      polarArg (p j) + 2 * Real.pi - polarArg (p i),
      Or.inl rfl, hδpos.le, ?_, Or.inr ?_, ?_⟩
    · rw [hfirst] at hminus
      rw [hprev]
      exact hminus.2
    · rw [hfirst] at hu
      linarith [hu, hright]
    · rw [cos_add_two_pi_sub_left]
      have hneg : polarArg (p j) - polarArg (p i) =
          -(polarArg (p i) - polarArg (p j)) := by ring
      rw [hneg, Real.cos_neg]

theorem actual_large_contact_local_gap_position (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hs : 2 ≤ ‖p i‖)
    (hj : ‖p j‖ = b) (hcontact : dist (p i) (p j) = 2) :
    ∃ (v : Fin (boundaryAngles p b).card) (θ δ : ℝ),
      (θ = polarArg (p i) ∨ θ = polarArg (p i) + 2 * Real.pi) ∧
      (47 / 100 : ℝ) < δ ∧ δ < Real.pi / 4 ∧
      2 * δ ≤ nextBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) v ∧
      (θ = (boundaryAngles p b).orderEmbOfFin rfl v + δ ∨
       θ = (boundaryAngles p b).orderEmbOfFin rfl v +
         nextBoundaryGap p b
           (by rw [boundaryAngles_card p b hsep]; omega) v - δ) ∧
      Real.cos δ = Real.cos (polarArg (p i) - polarArg (p j)) := by
  obtain ⟨v, θ, δ, hlift, hδ0, hsupport, hposition, hcos⟩ :=
    actual_contact_local_gap_position p b hb hbB hsep hD hK
      i j hi hj hcontact
  have hgaplt := every_next_gap_lt_pi p b (by linarith) hbB hsep hK v
  have hδhalf : δ < Real.pi / 2 := by linarith
  obtain ⟨hδlo, hδhi⟩ := actual_large_contact_offset_bounds (p i) (p j)
    b δ hb hbB hs (hD i hi) hj hcontact hδ0 hδhalf hcos
  exact ⟨v, θ, δ, hlift, hδlo, hδhi, hsupport, hposition, hcos⟩

/-- Complete local classification for two high-radius contacts placed in
one gap. Each center must lie in the half-gap next to one endpoint. Two
centers on the same side violate their pairwise angular separation; two on
opposite sides would make the gap exceed `12/7`. -/
theorem no_two_large_local_contacts_in_one_gap
    (x y : Plane) (left right θx θy δx δy : ℝ)
    (hxlo : 2 ≤ ‖x‖) (hxhi : ‖x‖ ≤ 12 / 5)
    (hylo : 2 ≤ ‖y‖) (hyhi : ‖y‖ ≤ 12 / 5)
    (hsep : 2 ≤ dist x y)
    (hlift : Real.cos (polarArg x - polarArg y) =
      Real.cos (θx - θy))
    (hgap : right - left < 12 / 7)
    (hδxlo : (47 / 100 : ℝ) < δx) (hδxhi : δx < Real.pi / 4)
    (hδylo : (47 / 100 : ℝ) < δy) (hδyhi : δy < Real.pi / 4)
    (hsupportx : 2 * δx ≤ right - left)
    (hsupporty : 2 * δy ≤ right - left)
    (hxposition : θx = left + δx ∨ θx = right - δx)
    (hyposition : θy = left + δy ∨ θy = right - δy) : False := by
  have hsepangle := large_inner_pair_angle_gt_four_fifths x y θx θy
    hxlo hxhi hylo hyhi hsep hlift
  have hpi : Real.pi / 4 < (4 / 5 : ℝ) := by
    have h := Real.pi_lt_d20
    linarith
  rcases hxposition with hxleft | hxright <;>
    rcases hyposition with hyleft | hyright
  · have hsmall : |θx - θy| < (4 / 5 : ℝ) := by
      apply abs_lt.mpr
      constructor <;> rw [hxleft, hyleft] <;> linarith
    linarith
  · have horder : θx ≤ θy := by
      rw [hxleft, hyright]
      linarith
    have hbig : (4 / 5 : ℝ) < θy - θx := by
      have habs : |θx - θy| = θy - θx := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [habs] at hsepangle
      exact hsepangle
    rw [hxleft, hyright] at hbig
    linarith
  · have horder : θy ≤ θx := by
      rw [hxright, hyleft]
      linarith
    have hbig : (4 / 5 : ℝ) < θx - θy := by
      have habs : |θx - θy| = θx - θy :=
        abs_of_nonneg (by linarith)
      rw [habs] at hsepangle
      exact hsepangle
    rw [hxright, hyleft] at hbig
    linarith
  · have hsmall : |θx - θy| < (4 / 5 : ℝ) := by
      apply abs_lt.mpr
      constructor <;> rw [hxright, hyright] <;> linarith
    linarith

/-- If two high-radius contacts are supported from opposite endpoints of
one gap, the actual center separation forces more than the sum of both
contact offsets plus `4/5` radians of gap width. This is the local spread
inequality used in the impossible opposite-side case. -/
theorem opposite_large_local_gap_gt_offset_sum
    (x y : Plane) (left right θx θy δx δy : ℝ)
    (hxlo : 2 ≤ ‖x‖) (hxhi : ‖x‖ ≤ 12 / 5)
    (hylo : 2 ≤ ‖y‖) (hyhi : ‖y‖ ≤ 12 / 5)
    (hsep : 2 ≤ dist x y)
    (hlift : Real.cos (polarArg x - polarArg y) =
      Real.cos (θx - θy))
    (hsupportx : 2 * δx ≤ right - left)
    (hsupporty : 2 * δy ≤ right - left)
    (hxposition : θx = left + δx)
    (hyposition : θy = right - δy) :
    δx + δy + 4 / 5 < right - left := by
  have hsepangle := large_inner_pair_angle_gt_four_fifths x y θx θy
    hxlo hxhi hylo hyhi hsep hlift
  have horder : θx ≤ θy := by
    rw [hxposition, hyposition]
    linarith
  have habs : |θx - θy| = θy - θx := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [habs, hxposition, hyposition] at hsepangle
  linarith

/-- The exact rational consequence of the opposite-side spread inequality
when each contact offset exceeds `47/100`. -/
theorem opposite_large_local_gap_gt_87_div_50
    (x y : Plane) (left right θx θy δx δy : ℝ)
    (hxlo : 2 ≤ ‖x‖) (hxhi : ‖x‖ ≤ 12 / 5)
    (hylo : 2 ≤ ‖y‖) (hyhi : ‖y‖ ≤ 12 / 5)
    (hsep : 2 ≤ dist x y)
    (hlift : Real.cos (polarArg x - polarArg y) =
      Real.cos (θx - θy))
    (hδx : (47 / 100 : ℝ) < δx)
    (hδy : (47 / 100 : ℝ) < δy)
    (hsupportx : 2 * δx ≤ right - left)
    (hsupporty : 2 * δy ≤ right - left)
    (hxposition : θx = left + δx)
    (hyposition : θy = right - δy) :
    (87 / 50 : ℝ) < right - left := by
  have hspread := opposite_large_local_gap_gt_offset_sum x y
    left right θx θy δx δy hxlo hxhi hylo hyhi hsep hlift
    hsupportx hsupporty hxposition hyposition
  linarith

/-- Two distinct inner centers of radius at least two, each touching the
outer ring, have distinct canonical gap charges. The theorem includes all
four contact orientations and the wrap gap through the local witness lemma. -/
theorem two_large_contacts_charge_distinct_gaps (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (i₁ j₁ i₂ j₂ : Fin 15) (hne : i₁ ≠ i₂)
    (hi₁ : ‖p i₁‖ < b) (hs₁ : 2 ≤ ‖p i₁‖)
    (hj₁ : ‖p j₁‖ = b) (htouch₁ : dist (p i₁) (p j₁) = 2)
    (hi₂ : ‖p i₂‖ < b) (hs₂ : 2 ≤ ‖p i₂‖)
    (hj₂ : ‖p j₂‖ = b) (htouch₂ : dist (p i₂) (p j₂) = 2) :
    ∃ v₁ v₂ : Fin (boundaryAngles p b).card,
      v₁ ≠ v₂ ∧
      ∃ δ₁ δ₂ : ℝ,
        (47 / 100 : ℝ) < δ₁ ∧
        2 * δ₁ ≤ nextBoundaryGap p b
          (by rw [boundaryAngles_card p b hsep]; omega) v₁ ∧
        (47 / 100 : ℝ) < δ₂ ∧
        2 * δ₂ ≤ nextBoundaryGap p b
          (by rw [boundaryAngles_card p b hsep]; omega) v₂ := by
  obtain ⟨v₁, θ₁, δ₁, hlift₁, hδ₁lo, hδ₁hi, hsupport₁,
    hposition₁, _⟩ := actual_large_contact_local_gap_position p b
      hb hbB hsep hD hK i₁ j₁ hi₁ hs₁ hj₁ htouch₁
  obtain ⟨v₂, θ₂, δ₂, hlift₂, hδ₂lo, hδ₂hi, hsupport₂,
    hposition₂, _⟩ := actual_large_contact_local_gap_position p b
      hb hbB hsep hD hK i₂ j₂ hi₂ hs₂ hj₂ htouch₂
  have hdistinct : v₁ ≠ v₂ := by
    intro hsame
    subst v₂
    have hDb := D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB
    have hr₁ : ‖p i₁‖ ≤ 12 / 5 := ((hD i₁ hi₁).trans hDb).le
    have hr₂ : ‖p i₂‖ ≤ 12 / 5 := ((hD i₂ hi₂).trans hDb).le
    have hcos := cos_diff_of_two_pi_lifts (p i₁) (p i₂) θ₁ θ₂
      hlift₁ hlift₂
    have hgap := every_next_gap_lt_twelve_sevenths p b
      (by linarith) hbB hsep hK v₁
    have hgap' :
        ((boundaryAngles p b).orderEmbOfFin rfl v₁ +
          nextBoundaryGap p b
            (by rw [boundaryAngles_card p b hsep]; omega) v₁) -
          (boundaryAngles p b).orderEmbOfFin rfl v₁ < 12 / 7 := by
      linarith
    have hsupport₁' : 2 * δ₁ ≤
        ((boundaryAngles p b).orderEmbOfFin rfl v₁ +
          nextBoundaryGap p b
            (by rw [boundaryAngles_card p b hsep]; omega) v₁) -
          (boundaryAngles p b).orderEmbOfFin rfl v₁ := by
      linarith
    have hsupport₂' : 2 * δ₂ ≤
        ((boundaryAngles p b).orderEmbOfFin rfl v₁ +
          nextBoundaryGap p b
            (by rw [boundaryAngles_card p b hsep]; omega) v₁) -
          (boundaryAngles p b).orderEmbOfFin rfl v₁ := by
      linarith
    exact no_two_large_local_contacts_in_one_gap (p i₁) (p i₂)
      ((boundaryAngles p b).orderEmbOfFin rfl v₁)
      ((boundaryAngles p b).orderEmbOfFin rfl v₁ +
        nextBoundaryGap p b
          (by rw [boundaryAngles_card p b hsep]; omega) v₁)
      θ₁ θ₂ δ₁ δ₂ hs₁ hr₁ hs₂ hr₂ (hsep i₁ i₂ hne)
      hcos hgap' hδ₁lo hδ₁hi hδ₂lo hδ₂hi
      hsupport₁' hsupport₂' hposition₁ hposition₂
  exact ⟨v₁, v₂, hdistinct, δ₁, δ₂,
    hδ₁lo, hsupport₁, hδ₂lo, hsupport₂⟩

/-- A single jointly chosen assignment for any finite family of high-radius
contacts has the complete collision classification: equal gap charges imply
equal inner centers. Repeated labels or several outer contacts of one inner
center may therefore share a gap, but distinct physical blockers cannot.
The proof includes both lifts across the polar branch cut. -/
theorem exists_large_contact_assignment_collision_implies_same_inner
    {ι : Type*} [Fintype ι]
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (inner outer : ι → Fin 15)
    (hinner : ∀ c, ‖p (inner c)‖ < b)
    (hradius : ∀ c, 2 ≤ ‖p (inner c)‖)
    (houter : ∀ c, ‖p (outer c)‖ = b)
    (htouch : ∀ c, dist (p (inner c)) (p (outer c)) = 2) :
    ∃ (charge : ι → Fin (boundaryAngles p b).card)
      (offset : ι → ℝ),
      (∀ a c, charge a = charge c → inner a = inner c) ∧
      ∀ c, (47 / 100 : ℝ) < offset c ∧
        2 * offset c ≤ nextBoundaryGap p b
          (by rw [boundaryAngles_card p b hsep]; omega) (charge c) ∧
        2 * ‖p (inner c)‖ * b * Real.cos (offset c) =
          b ^ 2 + ‖p (inner c)‖ ^ 2 - 4 := by
  classical
  let hsize : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  let witness (c : ι) := actual_large_contact_local_gap_position p b
    hb hbB hsep hD hK (inner c) (outer c)
      (hinner c) (hradius c) (houter c) (htouch c)
  let charge : ι → Fin (boundaryAngles p b).card :=
    fun c => Classical.choose (witness c)
  let angle : ι → ℝ :=
    fun c => Classical.choose (Classical.choose_spec (witness c))
  let offset : ι → ℝ :=
    fun c => Classical.choose (Classical.choose_spec
      (Classical.choose_spec (witness c)))
  have hdata (c : ι) :
      (angle c = polarArg (p (inner c)) ∨
        angle c = polarArg (p (inner c)) + 2 * Real.pi) ∧
      (47 / 100 : ℝ) < offset c ∧ offset c < Real.pi / 4 ∧
      2 * offset c ≤ nextBoundaryGap p b hsize (charge c) ∧
      (angle c = (boundaryAngles p b).orderEmbOfFin rfl (charge c) + offset c ∨
       angle c = (boundaryAngles p b).orderEmbOfFin rfl (charge c) +
         nextBoundaryGap p b hsize (charge c) - offset c) ∧
      Real.cos (offset c) =
        Real.cos (polarArg (p (inner c)) - polarArg (p (outer c))) := by
    exact Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (witness c)))
  have hlaw (c : ι) :
      2 * ‖p (inner c)‖ * b * Real.cos (offset c) =
        b ^ 2 + ‖p (inner c)‖ ^ 2 - 4 := by
    have h := contact_inner_formula (p (inner c)) (p (outer c)) b
      ‖p (inner c)‖ rfl (houter c) (htouch c)
    rw [polar_inner, houter c, ← (hdata c).2.2.2.2.2] at h
    nlinarith
  refine ⟨charge, offset, ?_, fun c =>
    ⟨(hdata c).2.1, (hdata c).2.2.2.1, hlaw c⟩⟩
  intro a c heq
  by_contra hinnerne
  obtain ⟨hlift₁, hδ₁lo, hδ₁hi, hsupport₁, hposition₁, _⟩ := hdata a
  obtain ⟨hlift₂, hδ₂lo, hδ₂hi, hsupport₂, hposition₂, _⟩ := hdata c
  have hDb := D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB
  have hr₁ : ‖p (inner a)‖ ≤ 12 / 5 := ((hD _ (hinner a)).trans hDb).le
  have hr₂ : ‖p (inner c)‖ ≤ 12 / 5 := ((hD _ (hinner c)).trans hDb).le
  have hcos := cos_diff_of_two_pi_lifts (p (inner a)) (p (inner c))
    (angle a) (angle c) hlift₁ hlift₂
  have hgap := every_next_gap_lt_twelve_sevenths p b
    (by linarith) hbB hsep hK (charge a)
  have hgap' :
      ((boundaryAngles p b).orderEmbOfFin rfl (charge a) +
        nextBoundaryGap p b hsize (charge a)) -
        (boundaryAngles p b).orderEmbOfFin rfl (charge a) < 12 / 7 := by
    linarith
  have hsupport₁' : 2 * offset a ≤
      ((boundaryAngles p b).orderEmbOfFin rfl (charge a) +
        nextBoundaryGap p b hsize (charge a)) -
        (boundaryAngles p b).orderEmbOfFin rfl (charge a) := by
    linarith
  have hsupport₂' : 2 * offset c ≤
      ((boundaryAngles p b).orderEmbOfFin rfl (charge a) +
        nextBoundaryGap p b hsize (charge a)) -
        (boundaryAngles p b).orderEmbOfFin rfl (charge a) := by
    rw [← heq] at hsupport₂
    linarith
  have hposition₂' :
      angle c = (boundaryAngles p b).orderEmbOfFin rfl (charge a) + offset c ∨
      angle c = (boundaryAngles p b).orderEmbOfFin rfl (charge a) +
        nextBoundaryGap p b hsize (charge a) - offset c := by
    rw [← heq] at hposition₂
    exact hposition₂
  exact no_two_large_local_contacts_in_one_gap
    (p (inner a)) (p (inner c))
    ((boundaryAngles p b).orderEmbOfFin rfl (charge a))
    ((boundaryAngles p b).orderEmbOfFin rfl (charge a) +
      nextBoundaryGap p b hsize (charge a))
    (angle a) (angle c) (offset a) (offset c)
    (hradius a) hr₁ (hradius c) hr₂
    (hsep (inner a) (inner c) hinnerne) hcos hgap'
    hδ₁lo hδ₁hi hδ₂lo hδ₂hi
    hsupport₁' hsupport₂' hposition₁ hposition₂'

/-- For a family indexed by distinct high-radius inner centers, the joint
assignment is injective. This rules out every two-way or three-way same-gap
collision among selected blockers. -/
theorem exists_injective_large_contact_assignment
    {ι : Type*} [Fintype ι]
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (inner outer : ι → Fin 15)
    (hinj : Function.Injective inner)
    (hinner : ∀ c, ‖p (inner c)‖ < b)
    (hradius : ∀ c, 2 ≤ ‖p (inner c)‖)
    (houter : ∀ c, ‖p (outer c)‖ = b)
    (htouch : ∀ c, dist (p (inner c)) (p (outer c)) = 2) :
    ∃ (charge : ι → Fin (boundaryAngles p b).card)
      (offset : ι → ℝ),
      Function.Injective charge ∧
      ∀ c, (47 / 100 : ℝ) < offset c ∧
        2 * offset c ≤ nextBoundaryGap p b
          (by rw [boundaryAngles_card p b hsep]; omega) (charge c) ∧
        2 * ‖p (inner c)‖ * b * Real.cos (offset c) =
          b ^ 2 + ‖p (inner c)‖ ^ 2 - 4 := by
  obtain ⟨charge, offset, hcollision, hdata⟩ :=
    exists_large_contact_assignment_collision_implies_same_inner
      p b hb hbB hsep hD hK inner outer hinner hradius houter htouch
  exact ⟨charge, offset, (fun _ _ heq => hinj (hcollision _ _ heq)), hdata⟩

end CP15
