import CP15.GapBudget

namespace CP15

/-- For one gap, take the maximum of its baseline demand and the support
demands of *all* assigned contacts. This definition retains contacts even
when several have the same gap index. -/
noncomputable def collisionDemand {ι : Type*} [DecidableEq ι] {K : ℕ}
    (α : ℝ) (contacts : Finset ι) (charge : ι → Fin K)
    (support : ι → ℝ) (u : Fin K) : ℝ := by
  classical
  let values : Finset ℝ :=
    insert α ((contacts.filter (fun c => charge c = u)).image
      (fun c => 2 * support c))
  exact values.sup' (by simp [values]) id

theorem baseline_le_collisionDemand {ι : Type*} [DecidableEq ι] {K : ℕ}
    (α : ℝ) (contacts : Finset ι) (charge : ι → Fin K)
    (support : ι → ℝ) (u : Fin K) :
    α ≤ collisionDemand α contacts charge support u := by
  classical
  let values : Finset ℝ :=
    insert α ((contacts.filter (fun c => charge c = u)).image
      (fun c => 2 * support c))
  have hmem : α ∈ values := by simp [values]
  change α ≤ values.sup' ⟨α, hmem⟩ id
  exact Finset.le_sup' id hmem

theorem assigned_support_le_collisionDemand {ι : Type*} [DecidableEq ι] {K : ℕ}
    (α : ℝ) (contacts : Finset ι) (charge : ι → Fin K)
    (support : ι → ℝ) (c : ι) (hc : c ∈ contacts) :
    2 * support c ≤ collisionDemand α contacts charge support (charge c) := by
  classical
  let values : Finset ℝ :=
    insert α ((contacts.filter (fun c_1 => charge c_1 = charge c)).image
      (fun c_1 => 2 * support c_1))
  have hmem : 2 * support c ∈ values := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, rfl⟩, rfl⟩
  change 2 * support c ≤ values.sup' ⟨α, by simp [values]⟩ id
  exact Finset.le_sup' id hmem

/-- The exact collision-safe accounting inequality for arbitrary finite
contact labels. If contacts share a gap, their demands are combined by a
maximum, not summed. No cardinality or injectivity premise is hidden. -/
theorem collision_budget_generic {ι : Type*} [DecidableEq ι] {K : ℕ}
    (α : ℝ) (contacts : Finset ι) (charge : ι → Fin K)
    (support : ι → ℝ) (gap : Fin K → ℝ)
    (hbaseline : ∀ u, α ≤ gap u)
    (hcontact : ∀ c ∈ contacts, 2 * support c ≤ gap (charge c)) :
    (∑ u : Fin K, collisionDemand α contacts charge support u) ≤
      ∑ u : Fin K, gap u := by
  classical
  apply Finset.sum_le_sum
  intro u _
  unfold collisionDemand
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with hbase | hvalue
  · subst x
    exact hbaseline u
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hvalue
    obtain ⟨hmember, hcharge⟩ := Finset.mem_filter.mp hc
    simpa [hcharge] using hcontact c hmember

/-- Actual cyclic gap budget at the candidate scale, including the closing
wrap gap. Every contact family is allowed: repeated contacts, repeated
centers, and arbitrary many labels charging one gap. -/
theorem collision_budget_actual {ι : Type*} [DecidableEq ι]
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 0 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (contacts : Finset ι)
    (charge : ι → Fin (boundaryAngles p b).card)
    (support : ι → ℝ)
    (hcontact : ∀ c ∈ contacts,
      2 * support c ≤ nextBoundaryGap p b hK (charge c)) :
    (∑ u : Fin (boundaryAngles p b).card,
      collisionDemand (4 / 7) contacts charge support u) ≤
        2 * Real.pi := by
  have h := collision_budget_generic (4 / 7 : ℝ) contacts charge support
    (nextBoundaryGap p b hK)
    (every_next_gap_ge_four_sevenths p b hb hbB hsep hK)
    hcontact
  rw [sum_next_boundary_gaps p b hK] at h
  exact h

/-- Explicit two-contact shared-gap case, valid also when `u` is the last
index and its forward gap is the polar wrap gap. The two support demands
contribute their maximum to that gap. -/
theorem two_contacts_same_gap_budget (p : Fin 15 → Plane) (b α γ₁ γ₂ : ℝ)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (u : Fin (boundaryAngles p b).card)
    (hbase : ∀ v, α ≤ nextBoundaryGap p b hK v)
    (h₁ : 2 * γ₁ ≤ nextBoundaryGap p b hK u)
    (h₂ : 2 * γ₂ ≤ nextBoundaryGap p b hK u) :
    max α (max (2 * γ₁) (2 * γ₂)) +
      (∑ _v ∈ Finset.univ.erase u, α) ≤ 2 * Real.pi := by
  classical
  have hshared : max α (max (2 * γ₁) (2 * γ₂)) ≤
      nextBoundaryGap p b hK u :=
    max_le (hbase u) (max_le h₁ h₂)
  have hother : (∑ _v ∈ Finset.univ.erase u, α) ≤
      ∑ v ∈ Finset.univ.erase u, nextBoundaryGap p b hK v :=
    Finset.sum_le_sum (fun v _ => hbase v)
  have hsum := sum_next_boundary_gaps p b hK
  rw [← Finset.add_sum_erase Finset.univ
    (nextBoundaryGap p b hK) (Finset.mem_univ u)] at hsum
  linarith

/-- A shared gap with ordered-contact spread `γ₁+γ₂+χ` pays at least the
two individual costs, once one freed baseline gap is credited. This is a
pure scalar lemma; the spread premise is a geometric obligation. -/
theorem shared_gap_spread_pays_two_costs (α γ₁ γ₂ χ Δ : ℝ)
    (hγ₁ : 0 ≤ γ₁ ∧ γ₁ ≤ α)
    (hγ₂ : 0 ≤ γ₂ ∧ γ₂ ≤ α)
    (hχ : α ≤ χ)
    (hspread : γ₁ + γ₂ + χ ≤ Δ) :
    max α (2 * γ₁) + max α (2 * γ₂) ≤ Δ + α := by
  rcases hγ₁ with ⟨hγ₁₀, hγ₁α⟩
  rcases hγ₂ with ⟨hγ₂₀, hγ₂α⟩
  by_cases h₁ : 2 * γ₁ ≤ α
  · by_cases h₂ : 2 * γ₂ ≤ α
    · rw [max_eq_left h₁, max_eq_left h₂]
      linarith
    · rw [max_eq_left h₁, max_eq_right (le_of_not_ge h₂)]
      linarith
  · by_cases h₂ : 2 * γ₂ ≤ α
    · rw [max_eq_right (le_of_not_ge h₁), max_eq_left h₂]
      linarith
    · rw [max_eq_right (le_of_not_ge h₁), max_eq_right (le_of_not_ge h₂)]
      linarith

/-- Explicit shared-gap budget with the pair spread premise. The subtraction
of one baseline charge is exactly the credit for combining two contacts in
one gap. The statement includes the closing gap because `u` is any cyclic
index. -/
theorem two_contacts_shared_gap_spread_budget
    (p : Fin 15 → Plane) (b α γ₁ γ₂ χ : ℝ)
    (hK : 2 ≤ (boundaryAngles p b).card)
    (u : Fin (boundaryAngles p b).card)
    (hbase : ∀ v, α ≤ nextBoundaryGap p b hK v)
    (hγ₁ : 0 ≤ γ₁ ∧ γ₁ ≤ α)
    (hγ₂ : 0 ≤ γ₂ ∧ γ₂ ≤ α)
    (hχ : α ≤ χ)
    (hspread : γ₁ + γ₂ + χ ≤ nextBoundaryGap p b hK u) :
    max α (2 * γ₁) + max α (2 * γ₂) +
      (∑ _v ∈ Finset.univ.erase u, α) - α ≤ 2 * Real.pi := by
  classical
  have hcost := shared_gap_spread_pays_two_costs α γ₁ γ₂ χ
    (nextBoundaryGap p b hK u) hγ₁ hγ₂ hχ hspread
  have hother : (∑ _v ∈ Finset.univ.erase u, α) ≤
      ∑ v ∈ Finset.univ.erase u, nextBoundaryGap p b hK v :=
    Finset.sum_le_sum (fun v _ => hbase v)
  have hsum := sum_next_boundary_gaps p b hK
  rw [← Finset.add_sum_erase Finset.univ
    (nextBoundaryGap p b hK) (Finset.mem_univ u)] at hsum
  linarith

/-- Every finite family of genuine inner–outer contacts admits a
collision-safe charge budget on the actual cyclic gaps. The family may
contain multiple labels for the same inner center or multiple contacts
with one outer center. The existential choice does not assume injectivity. -/
theorem exists_collision_safe_contact_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB) (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (hK : 9 ≤ (boundarySet p b).card)
    (inner outer : ι → Fin 15)
    (hinner : ∀ c, ‖p (inner c)‖ < b)
    (houter : ∀ c, ‖p (outer c)‖ = b)
    (htouch : ∀ c, dist (p (inner c)) (p (outer c)) = 2) :
    ∃ (charge : ι → Fin (boundaryAngles p b).card)
      (offset : ι → ℝ),
      (∀ c, 0 ≤ offset c ∧ offset c < Real.pi / 2 ∧
        2 * offset c ≤ nextBoundaryGap p b
          (by rw [boundaryAngles_card p b hsep]; omega) (charge c) ∧
        2 * ‖p (inner c)‖ * b * Real.cos (offset c) =
          b ^ 2 + ‖p (inner c)‖ ^ 2 - 4) ∧
      (∑ u : Fin (boundaryAngles p b).card,
        collisionDemand (4 / 7) Finset.univ charge offset u) ≤
          2 * Real.pi := by
  classical
  let hsize : 2 ≤ (boundaryAngles p b).card := by
    rw [boundaryAngles_card p b hsep]
    omega
  let witness (c : ι) := outer_contact_charged_cosine_law p b
    hb hbB hsep hD hK (inner c) (outer c)
      (hinner c) (houter c) (htouch c)
  let charge : ι → Fin (boundaryAngles p b).card :=
    fun c => Classical.choose (witness c)
  let offset : ι → ℝ :=
    fun c => Classical.choose (Classical.choose_spec (witness c))
  have hdata (c : ι) :
      0 ≤ offset c ∧ offset c < Real.pi / 2 ∧
      2 * offset c ≤ nextBoundaryGap p b hsize (charge c) ∧
      2 * ‖p (inner c)‖ * b * Real.cos (offset c) =
        b ^ 2 + ‖p (inner c)‖ ^ 2 - 4 := by
    exact Classical.choose_spec (Classical.choose_spec (witness c))
  refine ⟨charge, offset, hdata, ?_⟩
  exact collision_budget_actual p b (by linarith) hbB hsep hsize
    Finset.univ charge offset (fun c _ => (hdata c).2.2.1)

end CP15
