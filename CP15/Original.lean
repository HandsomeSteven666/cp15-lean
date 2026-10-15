import CP15.Definitions

/-!
The supremum of all feasible pairwise separations is the original d₁₅.
The predicate `PointOptimal` records both attainment and the upper bound.
-/

namespace CP15

/-- The distances indexed exactly by the original `i < j` condition. -/
def pairDistances (p : Fin 15 → Plane) : Set ℝ :=
  {t | ∃ i j : Fin 15, i < j ∧ t = dist (p i) (p j)}

theorem pairDistances_nonempty (p : Fin 15 → Plane) :
    (pairDistances p).Nonempty := by
  refine ⟨dist (p 0) (p 1), 0, 1, ?_, rfl⟩
  decide

theorem pairDistances_bddBelow (p : Fin 15 → Plane) :
    BddBelow (pairDistances p) := by
  refine ⟨0, ?_⟩
  intro t ht
  rcases ht with ⟨i, j, _, rfl⟩
  exact dist_nonneg

/-- The finite minimum in the original problem, written as an infimum. -/
noncomputable def minDistance (p : Fin 15 → Plane) : ℝ :=
  sInf (pairDistances p)

theorem separated_iff_le_minDistance (p : Fin 15 → Plane) (d : ℝ) :
    Separated p d ↔ d ≤ minDistance p := by
  constructor
  · intro hs
    apply le_csInf (pairDistances_nonempty p)
    intro t ht
    rcases ht with ⟨i, j, hij, rfl⟩
    exact hs i j (ne_of_lt hij)
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact h.trans (csInf_le (pairDistances_bddBelow p) ⟨i, j, hijlt, rfl⟩)
    · have h' := h.trans
        (csInf_le (pairDistances_bddBelow p) ⟨j, i, hjilt, rfl⟩)
      simpa [dist_comm] using h'

noncomputable def d15 : ℝ := sSup {d : ℝ | PointFeasible 15 d}

theorem pointFeasible_le_two {d : ℝ} (h : PointFeasible 15 d) : d ≤ 2 := by
  rcases h with ⟨p, hp, hs⟩
  have hsep : d ≤ dist (p 0) (p 1) := hs 0 1 (by decide)
  have htriangle : dist (p 0) (p 1) ≤ ‖p 0‖ + ‖p 1‖ :=
    by simpa [dist_eq_norm] using norm_sub_le (p 0) (p 1)
  have h0 := hp 0
  have h1 := hp 1
  linarith

/-- Literally the supremum, over fifteen points in the unit disk, of their
minimum pairwise distance. -/
noncomputable def originalValue : ℝ :=
  sSup {v : ℝ | ∃ p : Fin 15 → Plane, InUnitDisk p ∧ v = minDistance p}

theorem minDistance_feasible (p : Fin 15 → Plane) (hp : InUnitDisk p) :
    PointFeasible 15 (minDistance p) := by
  exact ⟨p, hp, (separated_iff_le_minDistance p _).2 le_rfl⟩

theorem originalValue_eq_d15 : originalValue = d15 := by
  let S : Set ℝ := {v | ∃ p : Fin 15 → Plane, InUnitDisk p ∧ v = minDistance p}
  let T : Set ℝ := {d | PointFeasible 15 d}
  have hS : S.Nonempty := by
    refine ⟨minDistance (fun _ => 0), (fun _ => 0), ?_, rfl⟩
    intro i
    simp
  have hT : T.Nonempty := by
    rcases hS with ⟨v, p, hp, rfl⟩
    exact ⟨minDistance p, minDistance_feasible p hp⟩
  have hS_bdd : BddAbove S := by
    refine ⟨2, ?_⟩
    intro v hv
    rcases hv with ⟨p, hp, rfl⟩
    exact pointFeasible_le_two (minDistance_feasible p hp)
  have hT_bdd : BddAbove T := by
    refine ⟨2, ?_⟩
    intro d hd
    exact pointFeasible_le_two hd
  change sSup S = sSup T
  apply le_antisymm
  · apply csSup_le hS
    intro v hv
    rcases hv with ⟨p, hp, rfl⟩
    exact le_csSup hT_bdd (minDistance_feasible p hp)
  · apply csSup_le hT
    intro d hd
    rcases hd with ⟨p, hp, hs⟩
    have hle : d ≤ minDistance p := (separated_iff_le_minDistance p d).1 hs
    exact hle.trans (le_csSup hS_bdd ⟨p, hp, rfl⟩)

theorem d15_eq_of_pointOptimal {d : ℝ} (h : PointOptimal 15 d) :
    d15 = d := by
  have hne : ({e : ℝ | PointFeasible 15 e}).Nonempty := ⟨d, h.1⟩
  apply le_antisymm
  · exact csSup_le hne (fun e he => h.2 e he)
  · exact le_csSup ⟨d, fun e he => h.2 e he⟩ h.1

end CP15
