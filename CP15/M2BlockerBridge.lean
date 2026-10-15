import CP15.HighRadiusBudget

open scoped InnerProductSpace

namespace CP15

private theorem pairMap_injective (a b : Fin 15) (hne : a ≠ b) :
    Function.Injective (fun c : Fin 2 => if c = 0 then a else b) := by
  intro c d h
  fin_cases c <;> fin_cases d <;> simp_all

/-- From two distinct non-outer centers in the selected radial-cap setting,
choose one strict blocker per center. The blockers either coincide, or their
actual outer contacts pay the exact two-cost cyclic budget. No assertion
about the shared-blocker branch is hidden in the disjunction. -/
theorem two_nonOuter_blocker_budget_or_shared
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
    (i₀ i₁ : Fin 15) (hne : i₀ ≠ i₁)
    (hi₀ : ‖p i₀‖ < b ∧ ¬TouchesOuter p b i₀)
    (hi₁ : ‖p i₁‖ < b ∧ ¬TouchesOuter p b i₁) :
    ∃ y₀ y₁ : Fin 15,
      y₀ ≠ i₀ ∧ dist (p i₀) (p y₀) = 2 ∧
      ‖p y₀‖ < b ∧ 2 < ‖p y₀‖ ∧ TouchesOuter p b y₀ ∧
      y₁ ≠ i₁ ∧ dist (p i₁) (p y₁) = 2 ∧
      ‖p y₁‖ < b ∧ 2 < ‖p y₁‖ ∧ TouchesOuter p b y₁ ∧
      (y₀ = y₁ ∨
        (y₀ ≠ y₁ ∧
          2 * Real.arccos
            ((b ^ 2 + ‖p y₀‖ ^ 2 - 4) / (2 * ‖p y₀‖ * b)) +
          2 * Real.arccos
            ((b ^ 2 + ‖p y₁‖ ^ 2 - 4) / (2 * ‖p y₁‖ * b)) +
          (((boundaryAngles p b).card : ℝ) - 2) * (4 / 7) ≤
            2 * Real.pi)) := by
  classical
  have hnz := nonOuter_pair_nonzero p b hpack.2 hFcap hFsmall
    i₀ i₁ hne hi₀ hi₁
  obtain ⟨y₀, hy₀ne, hiy₀, hy₀inner, hy₀high, hy₀touch, _⟩ :=
    nonOuter_blocker_touches_outer p b hpack hFcap hFsmall hblock
      i₀ hi₀.1 hi₀.2 hnz.1
  obtain ⟨y₁, hy₁ne, hiy₁, hy₁inner, hy₁high, hy₁touch, _⟩ :=
    nonOuter_blocker_touches_outer p b hpack hFcap hFsmall hblock
      i₁ hi₁.1 hi₁.2 hnz.2
  refine ⟨y₀, y₁, hy₀ne, hiy₀, hy₀inner, hy₀high, hy₀touch,
    hy₁ne, hiy₁, hy₁inner, hy₁high, hy₁touch, ?_⟩
  by_cases hsame : y₀ = y₁
  · exact Or.inl hsame
  · right
    obtain ⟨z₀, _, hz₀outer, hyz₀⟩ := hy₀touch
    obtain ⟨z₁, _, hz₁outer, hyz₁⟩ := hy₁touch
    let inner : Fin 2 → Fin 15 := fun c => if c = 0 then y₀ else y₁
    let outer : Fin 2 → Fin 15 := fun c => if c = 0 then z₀ else z₁
    have hinner : ∀ c, ‖p (inner c)‖ < b := by
      intro c
      fin_cases c <;> simp [inner, hy₀inner, hy₁inner]
    have hradius : ∀ c, 2 ≤ ‖p (inner c)‖ := by
      intro c
      fin_cases c <;> simp [inner, hy₀high.le, hy₁high.le]
    have houter : ∀ c, ‖p (outer c)‖ = b := by
      intro c
      fin_cases c <;> simp [outer, hz₀outer, hz₁outer]
    have htouch : ∀ c, dist (p (inner c)) (p (outer c)) = 2 := by
      intro c
      fin_cases c <;> simp [inner, outer, hyz₀, hyz₁]
    have hbudget := large_contact_arccos_card_budget p b hb hbB
      hpack.2 hD hK inner outer
      (pairMap_injective y₀ y₁ hsame) hinner hradius houter htouch
    refine ⟨hsame, ?_⟩
    simpa [Fin.sum_univ_two, inner] using hbudget

end CP15
