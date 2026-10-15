import CP15.SevenBoundaryShort
import CP15.CollisionGeometry

namespace CP15.SevenBoundary

/- The four actual polar-lift cases are replayed with K >= 7. This module
uses the original cyclic gap definitions and raw three-center geometry;
it does not posit a surrogate gap list or unique contact assignment. -/

theorem ordered_adjacent_contact_gap_doubling (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 7 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card)
    (hu : u.val + 1 < (boundaryAngles p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hmatch : polarArg (p j) =
      (boundaryAngles p b).orderEmbOfFin rfl u)
    (hcontact : dist (p i) (p j) = 2)
    (hforward : polarArg (p j) ≤ polarArg (p i))
    (hhalf : polarArg (p i) - polarArg (p j) ≤ Real.pi) :
    polarArg (p i) <
      (boundaryAngles p b).orderEmbOfFin rfl ⟨u.val + 1, hu⟩ ∧
      2 * (polarArg (p i) - polarArg (p j)) ≤
        (boundaryAngles p b).orderEmbOfFin rfl ⟨u.val + 1, hu⟩ -
          (boundaryAngles p b).orderEmbOfFin rfl u := by
  let s := boundaryAngles p b
  let e := s.orderEmbOfFin rfl
  let v : Fin s.card := ⟨u.val + 1, hu⟩
  have hv : e v ∈ s := Finset.orderEmbOfFin_mem s rfl v
  obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e v)).mp hv
  have huv : u < v := by
    change u.val < u.val + 1
    omega
  have hlt : e u < e v := e.strictMono huv
  have hjw : j ≠ w.val := by
    intro heq
    rw [heq] at hmatch
    linarith
  have hshort := ordered_boundary_adjacent_gap_lt_pi p b
    (by linarith) hbB hsep hK u hu
  have hresult := packing_contact_gap_doubling p b hb hsep hD
    i j w.val hi hj w.property hjw hcontact
    hforward hhalf (by dsimp [e] at hlt; linarith [hmatch, hw])
    (by simpa [s, e, v, hmatch, hw] using hshort)
  simpa only [hmatch, hw, s, e, v] using hresult


theorem ordered_previous_contact_gap_doubling (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 7 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card) (hu : 0 < u.val)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hmatch : polarArg (p j) =
      (boundaryAngles p b).orderEmbOfFin rfl u)
    (hcontact : dist (p i) (p j) = 2)
    (hbackward : polarArg (p i) ≤ polarArg (p j))
    (hhalf : polarArg (p j) - polarArg (p i) ≤ Real.pi) :
    (boundaryAngles p b).orderEmbOfFin rfl
      ⟨u.val - 1, by omega⟩ < polarArg (p i) ∧
      2 * (polarArg (p j) - polarArg (p i)) ≤
        (boundaryAngles p b).orderEmbOfFin rfl u -
          (boundaryAngles p b).orderEmbOfFin rfl
            ⟨u.val - 1, by omega⟩ := by
  let s := boundaryAngles p b
  let e := s.orderEmbOfFin rfl
  let v : Fin s.card := ⟨u.val - 1, by
    have hu' : u.val < s.card := u.isLt
    omega⟩
  have hv : e v ∈ s := Finset.orderEmbOfFin_mem s rfl v
  obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e v)).mp hv
  have huv : v < u := by
    change u.val - 1 < u.val
    omega
  have hlt : e v < e u := e.strictMono huv
  have hjw : j ≠ w.val := by
    intro heq
    rw [heq] at hmatch
    linarith
  have hvsucc : v.val + 1 < s.card := by
    change u.val - 1 + 1 < s.card
    have hu' : u.val < s.card := u.isLt
    omega
  have hshort' := ordered_boundary_adjacent_gap_lt_pi p b
    (by linarith) hbB hsep hK v hvsucc
  have hvsucc_eq : (⟨v.val + 1, hvsucc⟩ : Fin s.card) = u := by
    apply Fin.ext
    change u.val - 1 + 1 = u.val
    omega
  rw [hvsucc_eq] at hshort'
  have hresult := packing_contact_gap_doubling_backward p b hb hsep hD
    i j w.val hi hj w.property hjw hcontact
    hbackward hhalf (by dsimp [e] at hlt; linarith [hmatch, hw])
    (by simpa [s, e, v, hmatch, hw] using hshort')
  simpa only [hmatch, hw, s, e, v] using hresult


theorem forward_contact_charges_next_gap (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 7 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hmatch : polarArg (p j) =
      (boundaryAngles p b).orderEmbOfFin rfl u)
    (hcontact : dist (p i) (p j) = 2)
    (hforward : polarArg (p j) ≤ polarArg (p i))
    (hhalf : polarArg (p i) - polarArg (p j) ≤ Real.pi) :
    2 * (polarArg (p i) - polarArg (p j)) ≤
      nextBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) u := by
  have hsK : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  by_cases hu : u.val + 1 < (boundaryAngles p b).card
  · have h := (ordered_adjacent_contact_gap_doubling p b hb hbB hsep hD
      hK u hu i j hi hj hmatch hcontact hforward hhalf).2
    simpa [nextBoundaryGap, hu] using h
  · let s := boundaryAngles p b
    have hsK' : 2 ≤ s.card := hsK
    let e := s.orderEmbOfFin rfl
    let first : Fin s.card := ⟨0, by omega⟩
    have hfirst : e first ∈ s := Finset.orderEmbOfFin_mem s rfl first
    obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e first)).mp hfirst
    have huval : u.val = s.card - 1 := by
      have huis : u.val < s.card := u.isLt
      have hu' : ¬ u.val + 1 < s.card := hu
      omega
    have hfl : first < u := by
      change 0 < u.val
      omega
    have hlt : e first < e u := e.strictMono hfl
    have hjw : j ≠ w.val := by
      intro heq
      rw [heq] at hmatch
      linarith
    have hik : i ≠ w.val := by
      intro heq
      rw [heq, w.property] at hi
      exact (lt_irrefl b hi)
    have hne : p i ≠ 0 := by
      intro hzero
      have hd : dist (p i) (p j) = b := by
        rw [hzero, dist_zero_left, ← hj]
      linarith
    have hpos : 0 < ‖p i‖ := norm_pos_iff.mpr hne
    have hshort := ordered_boundary_wrap_gap_lt_pi p b
      (by linarith) hbB hsep hK
    have harglast : polarArg (p j) = e u := hmatch
    have hargfirst : polarArg (p w.val) = e first := hw
    have hright : polarArg (p j) ≤ polarArg (p w.val) + 2 * Real.pi := by
      have hr1 := polarArg_range (p j)
      have hr2 := polarArg_range (p w.val)
      linarith
    have hwrap' : polarArg (p w.val) + 2 * Real.pi - polarArg (p j) < Real.pi := by
      have hlast : u = (⟨s.card - 1, by omega⟩ : Fin s.card) := by
        apply Fin.ext
        exact huval
      simpa [s, e, first, hlast, harglast, hargfirst] using hshort
    have h := (contact_wrap_gap_doubling_lift
      (p i) (p j) (p w.val) b ‖p i‖ (polarArg (p i))
      (by linarith) hpos (hD i hi) rfl hj w.property hcontact
      (hsep i w.val hik) (hsep j w.val hjw)
      (.inl rfl) hforward hhalf hright hwrap').2
    simpa [nextBoundaryGap, hu, harglast, hargfirst, s, e, first] using h

/-- Same-principal-branch backward contact charges the actual previous gap,
including the wrap gap when its contact is the first boundary point. -/
theorem backward_contact_charges_previous_gap (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 7 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hmatch : polarArg (p j) =
      (boundaryAngles p b).orderEmbOfFin rfl u)
    (hcontact : dist (p i) (p j) = 2)
    (hbackward : polarArg (p i) ≤ polarArg (p j))
    (hhalf : polarArg (p j) - polarArg (p i) ≤ Real.pi) :
    2 * (polarArg (p j) - polarArg (p i)) ≤
      previousBoundaryGap p b
        (by rw [boundaryAngles_card p b hsep]; omega) u := by
  have hsK : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  by_cases hu : 0 < u.val
  · have h := (ordered_previous_contact_gap_doubling p b hb hbB hsep hD
      hK u hu i j hi hj hmatch hcontact hbackward hhalf).2
    simpa [previousBoundaryGap, hu] using h
  · let s := boundaryAngles p b
    have hsK' : 2 ≤ s.card := hsK
    let e := s.orderEmbOfFin rfl
    let last : Fin s.card := ⟨s.card - 1, by omega⟩
    have hlast : e last ∈ s := Finset.orderEmbOfFin_mem s rfl last
    obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e last)).mp hlast
    have huval : u.val = 0 := by omega
    have hfl : u < last := by
      change u.val < s.card - 1
      omega
    have hlt : e u < e last := e.strictMono hfl
    have hjw : j ≠ w.val := by
      intro heq
      rw [heq] at hmatch
      linarith
    have hik : i ≠ w.val := by
      intro heq
      rw [heq, w.property] at hi
      exact (lt_irrefl b hi)
    have hne : p i ≠ 0 := by
      intro hzero
      have hd : dist (p i) (p j) = b := by
        rw [hzero, dist_zero_left, ← hj]
      linarith
    have hpos : 0 < ‖p i‖ := norm_pos_iff.mpr hne
    have hshort := ordered_boundary_wrap_gap_lt_pi p b
      (by linarith) hbB hsep hK
    have hargfirst : polarArg (p j) = e u := hmatch
    have harglast : polarArg (p w.val) = e last := hw
    have hright : polarArg (p w.val) ≤ polarArg (p j) + 2 * Real.pi := by
      have hr1 := polarArg_range (p j)
      have hr2 := polarArg_range (p w.val)
      linarith
    have hwrap' : polarArg (p j) + 2 * Real.pi - polarArg (p w.val) < Real.pi := by
      have hfirst : u = (⟨0, by omega⟩ : Fin s.card) := by
        apply Fin.ext
        exact huval
      simpa [s, e, last, hfirst, hargfirst, harglast] using hshort
    have h := (contact_wrap_gap_doubling_lift_backward
      (p i) (p j) (p w.val) b ‖p i‖ (polarArg (p i) + 2 * Real.pi)
      (by linarith) hpos (hD i hi) rfl hj w.property hcontact
      (hsep i w.val hik) (hsep j w.val hjw)
      (.inr rfl) (by linarith [hbackward])
      (by linarith [hhalf]) hright hwrap').2
    simpa [previousBoundaryGap, hu, hargfirst, harglast, s, e, last] using h

/-- If the inner principal angle needs a `+2π` lift to be close to its
contacted outer point, then that outer point must be last in polar order.
The charged gap is consequently the wrap gap. -/
theorem forward_shifted_contact_charges_wrap_gap (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 7 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hmatch : polarArg (p j) =
      (boundaryAngles p b).orderEmbOfFin rfl u)
    (hcontact : dist (p i) (p j) = 2)
    (hshift : |(polarArg (p i) + 2 * Real.pi) - polarArg (p j)| < Real.pi / 2) :
    ¬ u.val + 1 < (boundaryAngles p b).card ∧
      2 * ((polarArg (p i) + 2 * Real.pi) - polarArg (p j)) ≤
        nextBoundaryGap p b
          (by rw [boundaryAngles_card p b hsep]; omega) u := by
  have hsK : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  let θq := polarArg (p i) + 2 * Real.pi
  have hside : polarArg (p j) < θq := by
    have hrq := polarArg_range (p i)
    have hrj := polarArg_range (p j)
    dsimp [θq]
    linarith
  have hhalf : θq - polarArg (p j) ≤ Real.pi := by
    have h := (abs_lt.mp hshift).2
    dsimp [θq]
    linarith
  have hne : p i ≠ 0 := by
    intro hzero
    have hd : dist (p i) (p j) = b := by
      rw [hzero, dist_zero_left, ← hj]
    linarith
  have hpos : 0 < ‖p i‖ := norm_pos_iff.mpr hne
  let s := boundaryAngles p b
  let e := s.orderEmbOfFin rfl
  by_cases hu : u.val + 1 < s.card
  · let v : Fin s.card := ⟨u.val + 1, hu⟩
    have hv : e v ∈ s := Finset.orderEmbOfFin_mem s rfl v
    obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e v)).mp hv
    have huv : u < v := by change u.val < u.val + 1; omega
    have hlt : e u < e v := e.strictMono huv
    have hjw : j ≠ w.val := by
      intro heq
      rw [heq] at hmatch
      linarith
    have hik : i ≠ w.val := by
      intro heq
      rw [heq, w.property] at hi
      exact (lt_irrefl b hi)
    have hshort := ordered_boundary_adjacent_gap_lt_pi p b
      (by linarith) hbB hsep hK u hu
    have hqz : Real.cos (polarArg (p i) - polarArg (p j)) =
        Real.cos (θq - polarArg (p j)) := by
      dsimp [θq]
      rw [cos_add_two_pi_sub_left]
    have hqw : Real.cos (polarArg (p i) - polarArg (p w.val)) =
        Real.cos (θq - polarArg (p w.val)) := by
      dsimp [θq]
      rw [cos_add_two_pi_sub_left]
    have hbefore := (contact_gap_doubling_lift
      (p i) (p j) (p w.val) b ‖p i‖ θq
      (polarArg (p j)) (polarArg (p w.val))
      (by linarith) hpos (hD i hi) rfl hj w.property hcontact
      (hsep i w.val hik) (hsep j w.val hjw)
      hqz hqw rfl hside.le hhalf
      (by linarith [hmatch, hw, hlt])
      (by simpa [s, e, v, hmatch, hw] using hshort)).1
    have hrw := (polarArg_range (p w.val)).2
    dsimp [θq] at hbefore
    have hrq := (polarArg_range (p i)).1
    linarith
  · have hsK' : 2 ≤ s.card := hsK
    refine ⟨hu, ?_⟩
    let first : Fin s.card := ⟨0, by omega⟩
    have hfirst : e first ∈ s := Finset.orderEmbOfFin_mem s rfl first
    obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e first)).mp hfirst
    have huval : u.val = s.card - 1 := by
      have huis : u.val < s.card := u.isLt
      omega
    have hfl : first < u := by change 0 < u.val; omega
    have hlt : e first < e u := e.strictMono hfl
    have hjw : j ≠ w.val := by
      intro heq
      rw [heq] at hmatch
      linarith
    have hik : i ≠ w.val := by
      intro heq
      rw [heq, w.property] at hi
      exact (lt_irrefl b hi)
    have hshort := ordered_boundary_wrap_gap_lt_pi p b
      (by linarith) hbB hsep hK
    have hright : polarArg (p j) ≤ polarArg (p w.val) + 2 * Real.pi := by
      have hr1 := polarArg_range (p j)
      have hr2 := polarArg_range (p w.val)
      linarith
    have hwrap' : polarArg (p w.val) + 2 * Real.pi - polarArg (p j) < Real.pi := by
      have hlast : u = (⟨s.card - 1, by omega⟩ : Fin s.card) := by
        apply Fin.ext
        exact huval
      simpa [s, e, first, hlast, hmatch, hw] using hshort
    have h := (contact_wrap_gap_doubling_lift
      (p i) (p j) (p w.val) b ‖p i‖ θq
      (by linarith) hpos (hD i hi) rfl hj w.property hcontact
      (hsep i w.val hik) (hsep j w.val hjw)
      (.inr rfl) hside.le hhalf hright hwrap').2
    simpa [nextBoundaryGap, hu, s, e, first, hmatch, hw, θq] using h

/-- A contact needing a `-2π` inner lift must be the first boundary point,
and charges the backward wrap gap. -/
theorem backward_shifted_contact_charges_wrap_gap (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 7 ≤ (boundarySet p b).card)
    (u : Fin (boundaryAngles p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hmatch : polarArg (p j) =
      (boundaryAngles p b).orderEmbOfFin rfl u)
    (hcontact : dist (p i) (p j) = 2)
    (hshift : |(polarArg (p i) - 2 * Real.pi) - polarArg (p j)| < Real.pi / 2) :
    ¬ 0 < u.val ∧
      2 * ((polarArg (p j) + 2 * Real.pi) - polarArg (p i)) ≤
        previousBoundaryGap p b
          (by rw [boundaryAngles_card p b hsep]; omega) u := by
  have hsK : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  let θq := polarArg (p i) - 2 * Real.pi
  have hside : θq < polarArg (p j) := by
    have hrq := polarArg_range (p i)
    have hrj := polarArg_range (p j)
    dsimp [θq]
    linarith
  have hhalf : polarArg (p j) - θq ≤ Real.pi := by
    have h := (abs_lt.mp hshift).1
    dsimp [θq]
    linarith
  have hne : p i ≠ 0 := by
    intro hzero
    have hd : dist (p i) (p j) = b := by
      rw [hzero, dist_zero_left, ← hj]
    linarith
  have hpos : 0 < ‖p i‖ := norm_pos_iff.mpr hne
  let s := boundaryAngles p b
  let e := s.orderEmbOfFin rfl
  by_cases hu : 0 < u.val
  · let v : Fin s.card := ⟨u.val - 1, by
      have huis : u.val < s.card := u.isLt
      omega⟩
    have hv : e v ∈ s := Finset.orderEmbOfFin_mem s rfl v
    obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e v)).mp hv
    have huv : v < u := by change u.val - 1 < u.val; omega
    have hlt : e v < e u := e.strictMono huv
    have hjw : j ≠ w.val := by
      intro heq
      rw [heq] at hmatch
      linarith
    have hik : i ≠ w.val := by
      intro heq
      rw [heq, w.property] at hi
      exact (lt_irrefl b hi)
    have hvsucc : v.val + 1 < s.card := by
      change u.val - 1 + 1 < s.card
      have huis : u.val < s.card := u.isLt
      omega
    have hshort' := ordered_boundary_adjacent_gap_lt_pi p b
      (by linarith) hbB hsep hK v hvsucc
    have hvsucc_eq : (⟨v.val + 1, hvsucc⟩ : Fin s.card) = u := by
      apply Fin.ext
      change u.val - 1 + 1 = u.val
      omega
    rw [hvsucc_eq] at hshort'
    have hqz : Real.cos (polarArg (p i) - polarArg (p j)) =
        Real.cos (θq - polarArg (p j)) := by
      dsimp [θq]
      rw [cos_sub_two_pi_sub_left]
    have hqw : Real.cos (polarArg (p i) - polarArg (p w.val)) =
        Real.cos (θq - polarArg (p w.val)) := by
      dsimp [θq]
      rw [cos_sub_two_pi_sub_left]
    have hafter := (contact_gap_doubling_lift_backward
      (p i) (p j) (p w.val) b ‖p i‖ θq
      (polarArg (p j)) (polarArg (p w.val))
      (by linarith) hpos (hD i hi) rfl hj w.property hcontact
      (hsep i w.val hik) (hsep j w.val hjw)
      hqz hqw rfl hside.le hhalf
      (by linarith [hmatch, hw, hlt])
      (by simpa [s, e, v, hmatch, hw] using hshort')).1
    have hrw := (polarArg_range (p w.val)).1
    dsimp [θq] at hafter
    have hrq := (polarArg_range (p i)).2
    linarith
  · have hsK' : 2 ≤ s.card := hsK
    refine ⟨hu, ?_⟩
    let last : Fin s.card := ⟨s.card - 1, by omega⟩
    have hlast : e last ∈ s := Finset.orderEmbOfFin_mem s rfl last
    obtain ⟨w, hw⟩ := (boundaryAngles_mem p b (e last)).mp hlast
    have huval : u.val = 0 := by omega
    have hfl : u < last := by change u.val < s.card - 1; omega
    have hlt : e u < e last := e.strictMono hfl
    have hjw : j ≠ w.val := by
      intro heq
      rw [heq] at hmatch
      linarith
    have hik : i ≠ w.val := by
      intro heq
      rw [heq, w.property] at hi
      exact (lt_irrefl b hi)
    have hshort := ordered_boundary_wrap_gap_lt_pi p b
      (by linarith) hbB hsep hK
    have hright : polarArg (p w.val) ≤ polarArg (p j) + 2 * Real.pi := by
      have hr1 := polarArg_range (p j)
      have hr2 := polarArg_range (p w.val)
      linarith
    have hwrap' : polarArg (p j) + 2 * Real.pi - polarArg (p w.val) < Real.pi := by
      have hfirst : u = (⟨0, by omega⟩ : Fin s.card) := by
        apply Fin.ext
        exact huval
      simpa [s, e, last, hfirst, hmatch, hw] using hshort
    have hside' : polarArg (p i) ≤ polarArg (p j) + 2 * Real.pi := by
      have hrq := polarArg_range (p i)
      have hrj := polarArg_range (p j)
      linarith
    have hhalf' : polarArg (p j) + 2 * Real.pi - polarArg (p i) ≤ Real.pi := by
      dsimp [θq] at hhalf
      linarith
    have h := (contact_wrap_gap_doubling_lift_backward
      (p i) (p j) (p w.val) b ‖p i‖ (polarArg (p i))
      (by linarith) hpos (hD i hi) rfl hj w.property hcontact
      (hsep i w.val hik) (hsep j w.val hjw)
      (.inl rfl) hside' hhalf' hright hwrap').2
    simpa [previousBoundaryGap, hu, s, e, last, hmatch, hw] using h

/-- Every inner-outer contact in a packing with at least nine boundary
centers charges one of the two adjacent cyclic gaps. The four alternatives
are forward, backward, forward across the branch cut, and backward across
the branch cut. This theorem does not assert that different contacts select
different gaps. -/
theorem every_outer_contact_charges_adjacent_gap (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 7 ≤ (boundarySet p b).card)
    (i j : Fin 15) (hi : ‖p i‖ < b) (hj : ‖p j‖ = b)
    (hcontact : dist (p i) (p j) = 2) :
    ∃ u : Fin (boundaryAngles p b).card,
      (boundaryAngles p b).orderEmbOfFin rfl u = polarArg (p j) ∧
      ((polarArg (p j) ≤ polarArg (p i) ∧
          2 * (polarArg (p i) - polarArg (p j)) ≤
            nextBoundaryGap p b
              (by rw [boundaryAngles_card p b hsep]; omega) u) ∨
       (polarArg (p i) ≤ polarArg (p j) ∧
          2 * (polarArg (p j) - polarArg (p i)) ≤
            previousBoundaryGap p b
              (by rw [boundaryAngles_card p b hsep]; omega) u) ∨
       (polarArg (p j) < polarArg (p i) + 2 * Real.pi ∧
          2 * ((polarArg (p i) + 2 * Real.pi) - polarArg (p j)) ≤
            nextBoundaryGap p b
              (by rw [boundaryAngles_card p b hsep]; omega) u) ∨
       (polarArg (p i) - 2 * Real.pi < polarArg (p j) ∧
          2 * ((polarArg (p j) + 2 * Real.pi) - polarArg (p i)) ≤
            previousBoundaryGap p b
              (by rw [boundaryAngles_card p b hsep]; omega) u)) := by
  obtain ⟨u, hu⟩ := boundary_center_has_sorted_index p b j hj
  refine ⟨u, hu, ?_⟩
  have hnear := inner_outer_contact_has_short_lift (p i) (p j) b hb hj hcontact
  rcases hnear with hplain | hplus | hminus
  · by_cases hforward : polarArg (p j) ≤ polarArg (p i)
    · left
      refine ⟨hforward, ?_⟩
      exact forward_contact_charges_next_gap p b hb hbB hsep hD hK
        u i j hi hj hu.symm hcontact hforward
        (by have h := (abs_lt.mp hplain).2; linarith)
    · right; left
      have hbackward : polarArg (p i) ≤ polarArg (p j) := by linarith
      refine ⟨hbackward, ?_⟩
      exact backward_contact_charges_previous_gap p b hb hbB hsep hD hK
        u i j hi hj hu.symm hcontact hbackward
        (by have h := (abs_lt.mp hplain).1; linarith)
  · right; right; left
    refine ⟨?_, (forward_shifted_contact_charges_wrap_gap p b hb hbB hsep hD
      hK u i j hi hj hu.symm hcontact hplus).2⟩
    have hrq := polarArg_range (p i)
    have hrj := polarArg_range (p j)
    linarith
  · right; right; right
    refine ⟨?_, (backward_shifted_contact_charges_wrap_gap p b hb hbB hsep hD
      hK u i j hi hj hu.symm hcontact hminus).2⟩
    have hrq := polarArg_range (p i)
    have hrj := polarArg_range (p j)
    linarith



theorem actual_contact_local_gap_position (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 7 ≤ (boundarySet p b).card)
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


end CP15.SevenBoundary
