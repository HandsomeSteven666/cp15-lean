import CP15.NonOuterBlockerFamily

open scoped InnerProductSpace

namespace CP15

theorem strict_contact_vector_inner_lt_neg_four
    (x y : Plane) (hcontact : dist x y = 2)
    (hblock : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ) :
    ⟪y, x - y⟫_ℝ < -4 := by
  have hsq : ‖x - y‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hcontact]
    norm_num
  rw [norm_sub_sq_real] at hsq
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  nlinarith [real_inner_comm x y]

theorem contact_vector_pair_inner_le_two
    (x z y : Plane) (hxy : dist x y = 2) (hzy : dist z y = 2)
    (hxz : 2 ≤ dist x z) :
    ⟪x - y, z - y⟫_ℝ ≤ 2 := by
  have hx : ‖x - y‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hxy]
    norm_num
  have hz : ‖z - y‖ ^ 2 = 4 := by
    rw [← dist_eq_norm, hzy]
    norm_num
  have hdist : 4 ≤ dist x z ^ 2 := by
    have hnonneg : 0 ≤ dist x z := dist_nonneg
    nlinarith
  have hsub : (x - y) - (z - y) = x - z := by abel
  have hsq : 4 ≤ ‖(x - y) - (z - y)‖ ^ 2 := by
    rw [hsub, ← dist_eq_norm]
    exact hdist
  rw [norm_sub_sq_real, hx, hz] at hsq
  linarith

/-- A radial threshold for one center to strictly block two
separated contact targets. Equality cannot occur because both blocking
inequalities are strict. -/
theorem two_strict_targets_force_blocker_sq_gt_sixteen_thirds
    (x z y : Plane)
    (hxy : dist x y = 2) (hzy : dist z y = 2)
    (hblockx : ‖x‖ ^ 2 < ⟪y, x⟫_ℝ)
    (hblockz : ‖z‖ ^ 2 < ⟪y, z⟫_ℝ)
    (hxz : 2 ≤ dist x z) : (16 / 3 : ℝ) < ‖y‖ ^ 2 := by
  let a := x - y
  let c := z - y
  let A := a + c
  have ha : ‖a‖ ^ 2 = 4 := by
    dsimp [a]
    rw [← dist_eq_norm, hxy]
    norm_num
  have hc : ‖c‖ ^ 2 = 4 := by
    dsimp [c]
    rw [← dist_eq_norm, hzy]
    norm_num
  have hp : ⟪a, c⟫_ℝ ≤ 2 :=
    contact_vector_pair_inner_le_two x z y hxy hzy hxz
  have hA : ‖A‖ ^ 2 ≤ 12 := by
    dsimp [A]
    rw [norm_add_sq_real]
    linarith
  have hd₀ : ⟪y, a⟫_ℝ < -4 :=
    strict_contact_vector_inner_lt_neg_four x y hxy hblockx
  have hd₁ : ⟪y, c⟫_ℝ < -4 :=
    strict_contact_vector_inner_lt_neg_four z y hzy hblockz
  have hdot : ⟪y, A⟫_ℝ < -8 := by
    dsimp [A]
    rw [inner_add_right]
    linarith
  have hcs : |⟪y, A⟫_ℝ| ≤ ‖y‖ * ‖A‖ :=
    abs_real_inner_le_norm y A
  have hprod : 8 < ‖y‖ * ‖A‖ := by
    have hneg : -⟪y, A⟫_ℝ ≤ |⟪y, A⟫_ℝ| := neg_le_abs _
    linarith
  have hmul := mul_le_mul_of_nonneg_left hA (sq_nonneg ‖y‖)
  nlinarith [sq_nonneg (‖y‖ * ‖A‖ - 8)]

/-- One inner center of radius below `12/5` cannot strictly block three
pairwise separated centers at contact distance two. This proof uses only
inner products, squared distances, and Cauchy–Schwarz; no angular ordering
or graph enumeration is involved. -/
theorem no_three_strict_targets_of_blocker_radius_lt_twelve_fifths
    (x₀ x₁ x₂ y : Plane)
    (hy : ‖y‖ < 12 / 5)
    (hc₀ : dist x₀ y = 2) (hc₁ : dist x₁ y = 2)
    (hc₂ : dist x₂ y = 2)
    (hb₀ : ‖x₀‖ ^ 2 < ⟪y, x₀⟫_ℝ)
    (hb₁ : ‖x₁‖ ^ 2 < ⟪y, x₁⟫_ℝ)
    (hb₂ : ‖x₂‖ ^ 2 < ⟪y, x₂⟫_ℝ)
    (h₀₁ : 2 ≤ dist x₀ x₁)
    (h₁₂ : 2 ≤ dist x₁ x₂)
    (h₂₀ : 2 ≤ dist x₂ x₀) : False := by
  let a₀ := x₀ - y
  let a₁ := x₁ - y
  let a₂ := x₂ - y
  let A := a₀ + a₁ + a₂
  have hnorm₀ : ‖a₀‖ ^ 2 = 4 := by
    dsimp [a₀]
    rw [← dist_eq_norm, hc₀]
    norm_num
  have hnorm₁ : ‖a₁‖ ^ 2 = 4 := by
    dsimp [a₁]
    rw [← dist_eq_norm, hc₁]
    norm_num
  have hnorm₂ : ‖a₂‖ ^ 2 = 4 := by
    dsimp [a₂]
    rw [← dist_eq_norm, hc₂]
    norm_num
  have hp₀₁ : ⟪a₀, a₁⟫_ℝ ≤ 2 :=
    contact_vector_pair_inner_le_two x₀ x₁ y hc₀ hc₁ h₀₁
  have hp₁₂ : ⟪a₁, a₂⟫_ℝ ≤ 2 :=
    contact_vector_pair_inner_le_two x₁ x₂ y hc₁ hc₂ h₁₂
  have hp₂₀ : ⟪a₂, a₀⟫_ℝ ≤ 2 :=
    contact_vector_pair_inner_le_two x₂ x₀ y hc₂ hc₀ h₂₀
  have hAexpand : ‖A‖ ^ 2 =
      ‖a₀‖ ^ 2 + ‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 +
        2 * ⟪a₀, a₁⟫_ℝ + 2 * ⟪a₁, a₂⟫_ℝ +
        2 * ⟪a₂, a₀⟫_ℝ := by
    dsimp [A]
    rw [norm_add_sq_real, norm_add_sq_real]
    rw [inner_add_left]
    rw [real_inner_comm a₀ a₂]
    ring
  have hA : ‖A‖ ^ 2 ≤ 24 := by linarith
  have hd₀ : ⟪y, a₀⟫_ℝ < -4 :=
    strict_contact_vector_inner_lt_neg_four x₀ y hc₀ hb₀
  have hd₁ : ⟪y, a₁⟫_ℝ < -4 :=
    strict_contact_vector_inner_lt_neg_four x₁ y hc₁ hb₁
  have hd₂ : ⟪y, a₂⟫_ℝ < -4 :=
    strict_contact_vector_inner_lt_neg_four x₂ y hc₂ hb₂
  have hdot : ⟪y, A⟫_ℝ < -12 := by
    dsimp [A]
    rw [inner_add_right, inner_add_right]
    linarith
  have hcs : |⟪y, A⟫_ℝ| ≤ ‖y‖ * ‖A‖ :=
    abs_real_inner_le_norm y A
  have hprod : 12 < ‖y‖ * ‖A‖ := by
    have hneg : -⟪y, A⟫_ℝ ≤ |⟪y, A⟫_ℝ| := neg_le_abs _
    linarith
  have hy2 : ‖y‖ ^ 2 < (12 / 5 : ℝ) ^ 2 := by
    have := norm_nonneg y
    nlinarith
  have hprod2 : (‖y‖ * ‖A‖) ^ 2 < (12 / 5 : ℝ) ^ 2 * 24 := by
    have hmul₁ := mul_le_mul_of_nonneg_left hA (sq_nonneg ‖y‖)
    have hmul₂ := mul_lt_mul_of_pos_right hy2 (by norm_num : (0 : ℝ) < 24)
    nlinarith [hmul₁, hmul₂]
  nlinarith [sq_nonneg (‖y‖ * ‖A‖ - 12)]

/-- In a candidate-scale separated packing, three distinct strict targets
cannot all select the same inner blocker. In particular, the `m = 3`
incidence type with one blocker for all three is impossible. -/
theorem three_selected_targets_not_one_blocker
    (p : Fin 15 → Plane) (b : ℝ)
    (hb : 2 < b) (hbB : b ≤ candidateB)
    (hsep : Separated p 2)
    (hD : ∀ t, ‖p t‖ < b → ‖p t‖ < D b)
    (target blocker : Fin 3 → Fin 15)
    (htarget : Function.Injective target)
    (hinner : ∀ c, ‖p (blocker c)‖ < b)
    (hcontact : ∀ c, dist (p (target c)) (p (blocker c)) = 2)
    (hstrict : ∀ c, ‖p (target c)‖ ^ 2 <
      ⟪p (blocker c), p (target c)⟫_ℝ) :
    ¬(blocker 0 = blocker 1 ∧ blocker 1 = blocker 2) := by
  intro hsame
  have h₀₁ : target 0 ≠ target 1 :=
    fun h => (by decide : (0 : Fin 3) ≠ 1) (htarget h)
  have h₁₂ : target 1 ≠ target 2 :=
    fun h => (by decide : (1 : Fin 3) ≠ 2) (htarget h)
  have h₂₀ : target 2 ≠ target 0 :=
    fun h => (by decide : (2 : Fin 3) ≠ 0) (htarget h)
  have hy : ‖p (blocker 0)‖ < 12 / 5 :=
    (hD _ (hinner 0)).trans
      (D_lt_twelve_fifths_of_le_candidateB b (by linarith) hbB)
  apply no_three_strict_targets_of_blocker_radius_lt_twelve_fifths
    (p (target 0)) (p (target 1)) (p (target 2)) (p (blocker 0)) hy
      (hcontact 0)
      (by simpa [← hsame.1] using hcontact 1)
      (by simpa [← hsame.2, ← hsame.1] using hcontact 2)
      (hstrict 0)
      (by simpa [← hsame.1] using hstrict 1)
      (by simpa [← hsame.2, ← hsame.1] using hstrict 2)
      (hsep _ _ h₀₁) (hsep _ _ h₁₂) (hsep _ _ h₂₀)

/-- Three distinct non-outer centers in the selected representative have
strict high-radius blockers, and no choice of the three selected blockers
can have the one-blocker incidence pattern. The additive budget is also
available in the all-distinct branch. -/
theorem three_nonOuter_blockers_not_all_shared
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
    (target : Fin 3 → Fin 15) (hinj : Function.Injective target)
    (hno : ∀ c, ‖p (target c)‖ < b ∧
      ¬TouchesOuter p b (target c)) :
    ∃ blocker : Fin 3 → Fin 15,
      (∀ c, ‖p (blocker c)‖ < b ∧ 2 < ‖p (blocker c)‖ ∧
        TouchesOuter p b (blocker c) ∧
        dist (p (target c)) (p (blocker c)) = 2 ∧
        ‖p (target c)‖ ^ 2 <
          ⟪p (blocker c), p (target c)⟫_ℝ) ∧
      ¬(blocker 0 = blocker 1 ∧ blocker 1 = blocker 2) ∧
      (Function.Injective blocker →
        (∑ c : Fin 3, 2 * Real.arccos
          ((b ^ 2 + ‖p (blocker c)‖ ^ 2 - 4) /
            (2 * ‖p (blocker c)‖ * b))) +
          (((boundaryAngles p b).card : ℝ) - 3) * (4 / 7) ≤
            2 * Real.pi) := by
  classical
  have h₀₁ : target 0 ≠ target 1 :=
    fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have h₂₀ : target 2 ≠ target 0 :=
    fun h => (by decide : (2 : Fin 3) ≠ 0) (hinj h)
  have hnz₀₁ := nonOuter_pair_nonzero p b hpack.2 hFcap hFsmall
    (target 0) (target 1) h₀₁ (hno 0) (hno 1)
  have hnz₂ := (nonOuter_pair_nonzero p b hpack.2 hFcap hFsmall
    (target 2) (target 0) h₂₀ (hno 2) (hno 0)).1
  have htarget (c : Fin 3) : ‖p (target c)‖ < b ∧
      ¬TouchesOuter p b (target c) ∧ p (target c) ≠ 0 := by
    fin_cases c
    · exact ⟨(hno 0).1, (hno 0).2, hnz₀₁.1⟩
    · exact ⟨(hno 1).1, (hno 1).2, hnz₀₁.2⟩
    · exact ⟨(hno 2).1, (hno 2).2, hnz₂⟩
  obtain ⟨blocker, outer, hdata, hbudget⟩ :=
    exists_nonOuter_blocker_family_with_conditional_budget p b hb hbB
      hpack hD hFcap hFsmall hblock hK target htarget
  refine ⟨blocker, ?_, ?_, ?_⟩
  · intro c
    exact ⟨(hdata c).2.2.1, (hdata c).2.2.2.1,
      ⟨outer c, (hdata c).2.2.2.2.1,
        (hdata c).2.2.2.2.2.1, (hdata c).2.2.2.2.2.2.1⟩,
      (hdata c).2.1, (hdata c).2.2.2.2.2.2.2⟩
  · exact three_selected_targets_not_one_blocker p b hb hbB hpack.2 hD
      target blocker hinj
      (fun c => (hdata c).2.2.1)
      (fun c => (hdata c).2.1)
      (fun c => (hdata c).2.2.2.2.2.2.2)
  · intro hblockinj
    simpa using hbudget hblockinj

/-- Exhaustive labeled incidence split for three selected blockers once the
single-blocker pattern is excluded. The first three cases have a shared
pair; the last has three distinct blockers. -/
theorem three_blocker_incidence_split
    (b₀ b₁ b₂ : Fin 15)
    (hnotall : ¬(b₀ = b₁ ∧ b₁ = b₂)) :
    (b₀ = b₁ ∧ b₁ ≠ b₂) ∨
    (b₀ = b₂ ∧ b₀ ≠ b₁) ∨
    (b₁ = b₂ ∧ b₀ ≠ b₁) ∨
    (b₀ ≠ b₁ ∧ b₀ ≠ b₂ ∧ b₁ ≠ b₂) := by
  by_cases h₀₁ : b₀ = b₁
  · left
    exact ⟨h₀₁, fun h₁₂ => hnotall ⟨h₀₁, h₁₂⟩⟩
  · by_cases h₀₂ : b₀ = b₂
    · exact Or.inr (Or.inl ⟨h₀₂, h₀₁⟩)
    · by_cases h₁₂ : b₁ = b₂
      · exact Or.inr (Or.inr (Or.inl ⟨h₁₂, h₀₁⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h₀₁, h₀₂, h₁₂⟩))

end CP15
