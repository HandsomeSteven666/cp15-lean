import CP15.CollisionGeometry

namespace CP15

/-- A finite injective charge assigns separate costs to separate gaps. The
complement is counted exactly once, including the closing cyclic gap. -/
theorem injective_gap_budget
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (s : Finset κ) (charge : ι → κ) (cost : ι → ℝ)
    (gap : κ → ℝ) (α total : ℝ)
    (hinj : Function.Injective charge)
    (hsubset : Finset.univ.image charge ⊆ s)
    (hcost : ∀ c, cost c ≤ gap (charge c))
    (hbase : ∀ u ∈ s \ Finset.univ.image charge, α ≤ gap u)
    (hsum : (∑ u ∈ s, gap u) = total) :
    (∑ c : ι, cost c) +
      (∑ _u ∈ s \ Finset.univ.image charge, α) ≤ total := by
  classical
  have himage :
      (∑ u ∈ Finset.univ.image charge, gap u) =
        ∑ c : ι, gap (charge c) := by
    rw [Finset.sum_image]
    intro a _ c _ h
    exact hinj h
  have hcostsum : (∑ c : ι, cost c) ≤
      ∑ c : ι, gap (charge c) :=
    Finset.sum_le_sum (fun c _ => hcost c)
  have hbasesum : (∑ _u ∈ s \ Finset.univ.image charge, α) ≤
      ∑ u ∈ s \ Finset.univ.image charge, gap u :=
    Finset.sum_le_sum hbase
  have hdisj : Disjoint (Finset.univ.image charge)
      (s \ Finset.univ.image charge) := Finset.disjoint_sdiff
  have hcover : (Finset.univ.image charge) ∪
      (s \ Finset.univ.image charge) = s :=
    Finset.union_sdiff_of_subset hsubset
  have hpartition :
      (∑ u ∈ Finset.univ.image charge, gap u) +
      (∑ u ∈ s \ Finset.univ.image charge, gap u) = total := by
    rw [← Finset.sum_union hdisj, hcover, hsum]
  linarith

/-- The actual outer ring pays twice the offset of each distinct high-radius
contacting inner center, plus `4/7` for every uncharged cyclic gap. The same
offset satisfies the exact contact cosine law. -/
theorem exists_large_contact_exact_gap_budget
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
      (∀ c, (47 / 100 : ℝ) < offset c ∧
        2 * offset c ≤ nextBoundaryGap p b
          (by rw [boundaryAngles_card p b hsep]; omega) (charge c) ∧
        2 * ‖p (inner c)‖ * b * Real.cos (offset c) =
          b ^ 2 + ‖p (inner c)‖ ^ 2 - 4) ∧
      (∑ c : ι, 2 * offset c) +
        (∑ _u ∈ Finset.univ \ Finset.univ.image charge,
          (4 / 7 : ℝ)) ≤ 2 * Real.pi ∧
      (∀ c, offset c = Real.arccos
        ((b ^ 2 + ‖p (inner c)‖ ^ 2 - 4) /
          (2 * ‖p (inner c)‖ * b))) := by
  classical
  obtain ⟨charge, offset, hcharge, hdata⟩ :=
    exists_injective_large_contact_assignment p b hb hbB hsep hD hK
      inner outer hinj hinner hradius houter htouch
  let hsize : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  refine ⟨charge, offset, hcharge, hdata, ?_, ?_⟩
  · exact injective_gap_budget Finset.univ charge (fun c => 2 * offset c)
      (nextBoundaryGap p b hsize) (4 / 7) (2 * Real.pi)
      hcharge (by simp) (fun c => (hdata c).2.1)
      (fun u _ => every_next_gap_ge_four_sevenths p b
        (by linarith) hbB hsep hsize u)
      (sum_next_boundary_gaps p b hsize)
  · intro c
    have hδ0 : 0 ≤ offset c := by linarith [(hdata c).1]
    have hδpi : offset c ≤ Real.pi := by
      have hgap := every_next_gap_lt_pi p b
        (by linarith) hbB hsep hK (charge c)
      linarith [(hdata c).2.1]
    have hfactor : 0 < 2 * ‖p (inner c)‖ * b := by
      have := hradius c
      positivity
    have hcos : Real.cos (offset c) =
        (b ^ 2 + ‖p (inner c)‖ ^ 2 - 4) /
          (2 * ‖p (inner c)‖ * b) := by
      apply (eq_div_iff hfactor.ne').2
      calc
        Real.cos (offset c) * (2 * ‖p (inner c)‖ * b) =
            2 * ‖p (inner c)‖ * b * Real.cos (offset c) := by ring
        _ = _ := (hdata c).2.2
    calc
      offset c = Real.arccos (Real.cos (offset c)) :=
        (Real.arccos_cos hδ0 hδpi).symm
      _ = _ := by rw [hcos]

/-- Radius-sensitive outer-ring budget for any finite family of distinct
high-radius inner centers with chosen actual outer contacts. There is no
remaining offset variable in the conclusion. -/
theorem exists_large_contact_arccos_budget
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
    ∃ charge : ι → Fin (boundaryAngles p b).card,
      Function.Injective charge ∧
      (∑ c : ι, 2 * Real.arccos
        ((b ^ 2 + ‖p (inner c)‖ ^ 2 - 4) /
          (2 * ‖p (inner c)‖ * b))) +
        (∑ _u ∈ Finset.univ \ Finset.univ.image charge,
          (4 / 7 : ℝ)) ≤ 2 * Real.pi := by
  classical
  obtain ⟨charge, offset, hinjcharge, _, hbudget, hexact⟩ :=
    exists_large_contact_exact_gap_budget p b hb hbB hsep hD hK
      inner outer hinj hinner hradius houter htouch
  refine ⟨charge, hinjcharge, ?_⟩
  have hsum :
      (∑ c : ι, 2 * Real.arccos
        ((b ^ 2 + ‖p (inner c)‖ ^ 2 - 4) /
          (2 * ‖p (inner c)‖ * b))) =
        ∑ c : ι, 2 * offset c := by
    apply Finset.sum_congr rfl
    intro c _
    rw [hexact c]
  rw [hsum]
  exact hbudget

/-- The injective charge also certifies the exact number of uncharged gaps.
This is the additive form used by the paper cost inequalities. -/
theorem large_contact_arccos_card_budget
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
    (∑ c : ι, 2 * Real.arccos
      ((b ^ 2 + ‖p (inner c)‖ ^ 2 - 4) /
        (2 * ‖p (inner c)‖ * b))) +
      (((boundaryAngles p b).card : ℝ) - (Fintype.card ι : ℝ)) * (4 / 7) ≤
        2 * Real.pi := by
  classical
  obtain ⟨charge, hcharge, hbudget⟩ :=
    exists_large_contact_arccos_budget p b hb hbB hsep hD hK
      inner outer hinj hinner hradius houter htouch
  have hsubset : Finset.univ.image charge ⊆
      (Finset.univ : Finset (Fin (boundaryAngles p b).card)) := by simp
  have hcard : ((Finset.univ \ Finset.univ.image charge).card : ℝ) =
      ((boundaryAngles p b).card : ℝ) - (Fintype.card ι : ℝ) := by
    rw [Finset.cast_card_sdiff hsubset]
    simp [Finset.card_image_of_injective _ hcharge]
  have hconst : (∑ _u ∈ Finset.univ \ Finset.univ.image charge,
        (4 / 7 : ℝ)) =
      (((boundaryAngles p b).card : ℝ) - (Fintype.card ι : ℝ)) *
        (4 / 7) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hcard]
  rwa [hconst] at hbudget

/-- The number of selected high-radius contacts cannot exceed the number
of actual cyclic outer gaps. This discharges the nonnegative `K−t` premise
when the preceding budget is used in a scalar comparison. -/
theorem large_contact_count_le_boundary_count
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
    Fintype.card ι ≤ (boundaryAngles p b).card := by
  obtain ⟨charge, _, hcharge, _⟩ :=
    exists_large_contact_exact_gap_budget p b hb hbB hsep hD hK
      inner outer hinj hinner hradius houter htouch
  simpa using Fintype.card_le_of_injective charge hcharge

end CP15
