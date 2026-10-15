import CP15.ComponentAscent
import CP15.GlobalUniquenessOrbitTransport

namespace CP15

/-- Decode a position in the order left, inner, right, left, inner, right,
... into the actual-cycle tags used by `actualAllIndex`. -/
def alternatingTagAtPosition (j : Fin 15) : Fin 5 ⊕ (Fin 5 ⊕ Fin 5) :=
  let i : Fin 5 := ⟨j.val / 3, by omega⟩
  if j.val % 3 = 0 then Sum.inr (Sum.inl i)
  else if j.val % 3 = 1 then Sum.inl i
  else Sum.inr (Sum.inr i)

/-- The lifted direction assigned to a position in the alternating order.
The final outer direction is lifted by one full turn only when the occupied
gaps have odd parity. -/
noncomputable def terminalAlternatingLift
    (ψ : Fin 10 → ℝ) (u : Fin 5 → Fin 10) (φ : Fin 5 → ℝ)
    (j : Fin 15) : ℝ :=
  let i : Fin 5 := ⟨j.val / 3, by omega⟩
  if j.val % 3 = 0 then ψ (u i)
  else if j.val % 3 = 1 then φ i
  else if u i = Fin.last 9 then ψ 0 + 2 * Real.pi else ψ (u i + 1)

theorem alternatingTagAtPosition_left (i : Fin 5) :
    alternatingTagAtPosition (alternatingLeft i) = Sum.inr (Sum.inl i) := by
  simp [alternatingTagAtPosition, alternatingLeft]

theorem alternatingTagAtPosition_inner (i : Fin 5) :
    alternatingTagAtPosition (alternatingInner i) = Sum.inl i := by
  have hdiv : (⟨(3 * i.val + 1) / 3, by omega⟩ : Fin 5) = i := by
    apply Fin.ext
    simp
    omega
  simp [alternatingTagAtPosition, alternatingInner, hdiv]

theorem alternatingTagAtPosition_right (i : Fin 5) :
    alternatingTagAtPosition (alternatingRight i) = Sum.inr (Sum.inr i) := by
  have hdiv : (⟨(3 * i.val + 2) / 3, by omega⟩ : Fin 5) = i := by
    apply Fin.ext
    simp
    omega
  simp [alternatingTagAtPosition, alternatingRight, hdiv]

theorem alternatingTagAtPosition_bijective :
    Function.Bijective alternatingTagAtPosition := by
  decide

def actualAlternatingIndex
    (ix : Fin 5 → Fin 15) (o : Fin 10 → Fin 15)
    (u : Fin 5 → Fin 10) (j : Fin 15) : Fin 15 :=
  actualAllIndex ix o u (alternatingTagAtPosition j)

theorem actualAlternatingIndex_left
    (ix : Fin 5 → Fin 15) (o : Fin 10 → Fin 15)
    (u : Fin 5 → Fin 10) (i : Fin 5) :
    actualAlternatingIndex ix o u (alternatingLeft i) = o (u i) := by
  simp [actualAlternatingIndex, alternatingTagAtPosition_left, actualAllIndex]

theorem actualAlternatingIndex_inner
    (ix : Fin 5 → Fin 15) (o : Fin 10 → Fin 15)
    (u : Fin 5 → Fin 10) (i : Fin 5) :
    actualAlternatingIndex ix o u (alternatingInner i) = ix i := by
  simp [actualAlternatingIndex, alternatingTagAtPosition_inner, actualAllIndex]

theorem actualAlternatingIndex_right
    (ix : Fin 5 → Fin 15) (o : Fin 10 → Fin 15)
    (u : Fin 5 → Fin 10) (i : Fin 5) :
    actualAlternatingIndex ix o u (alternatingRight i) = o (u i + 1) := by
  simp [actualAlternatingIndex, alternatingTagAtPosition_right, actualAllIndex]

theorem actualAlternatingIndex_bijective
    (ix : Fin 5 → Fin 15) (o : Fin 10 → Fin 15)
    (u : Fin 5 → Fin 10)
    (hactual : Function.Bijective (actualAllIndex ix o u)) :
    Function.Bijective (actualAlternatingIndex ix o u) := by
  constructor
  · intro i j hij
    apply alternatingTagAtPosition_bijective.1
    apply hactual.1
    exact hij
  · intro j
    obtain ⟨x, hx⟩ := hactual.2 j
    obtain ⟨i, hi⟩ := alternatingTagAtPosition_bijective.2 x
    exact ⟨i, by simpa [actualAlternatingIndex, hi] using hx⟩

noncomputable def actualAlternatingEquiv
    (ix : Fin 5 → Fin 15) (o : Fin 10 → Fin 15)
    (u : Fin 5 → Fin 10)
    (hactual : Function.Bijective (actualAllIndex ix o u)) :
    Fin 15 ≃ Fin 15 :=
  Equiv.ofBijective (actualAlternatingIndex ix o u)
    (actualAlternatingIndex_bijective ix o u hactual)

def actualAlternatingConfig (q : Fin 15 → Plane)
    (ix : Fin 5 → Fin 15) (o : Fin 10 → Fin 15)
    (u : Fin 5 → Fin 10) (j : Fin 15) : Plane :=
  q (actualAlternatingIndex ix o u j)

theorem actualAlternatingConfig_congruent
    (q : Fin 15 → Plane) (ix : Fin 5 → Fin 15)
    (o : Fin 10 → Fin 15) (u : Fin 5 → Fin 10)
    (hactual : Function.Bijective (actualAllIndex ix o u)) :
    CenteredCongruent15 (actualAlternatingConfig q ix o u) q := by
  refine ⟨actualAlternatingEquiv ix o u hactual,
    LinearIsometryEquiv.refl ℝ Plane, ?_⟩
  intro i
  rfl

theorem alternating_position_complete (j : Fin 15) :
    (∃ i, j = alternatingLeft i) ∨
      (∃ i, j = alternatingInner i) ∨
      ∃ i, j = alternatingRight i := by
  let i : Fin 5 := ⟨j.val / 3, by omega⟩
  have hmod : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
  rcases hmod with hmod | hmod | hmod
  · left
    refine ⟨i, ?_⟩
    apply Fin.ext
    simp [i, alternatingLeft]
    omega
  · right
    left
    refine ⟨i, ?_⟩
    apply Fin.ext
    simp [i, alternatingInner]
    omega
  · right
    right
    refine ⟨i, ?_⟩
    apply Fin.ext
    simp [i, alternatingRight]
    omega

theorem planeComplex_eq_realPolar (x : Plane) (θ : ℝ)
    (hθ : θ = polarArg x ∨ θ = polarArg x + 2 * Real.pi) :
    planeComplex x = ((‖x‖ : ℝ) : ℂ) *
      (Real.cos θ + Real.sin θ * Complex.I) := by
  have h := planeComplex_eq_polar_coordinates x θ hθ
  rw [h]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re]

theorem terminalAlternatingLift_left (ψ : Fin 10 → ℝ)
    (u : Fin 5 → Fin 10) (φ : Fin 5 → ℝ) (i : Fin 5) :
    terminalAlternatingLift ψ u φ (alternatingLeft i) = ψ (u i) := by
  simp [terminalAlternatingLift, alternatingLeft]

theorem terminalAlternatingLift_inner (ψ : Fin 10 → ℝ)
    (u : Fin 5 → Fin 10) (φ : Fin 5 → ℝ) (i : Fin 5) :
    terminalAlternatingLift ψ u φ (alternatingInner i) = φ i := by
  have hdiv : (⟨(3 * i.val + 1) / 3, by omega⟩ : Fin 5) = i := by
    apply Fin.ext
    simp
    omega
  simp [terminalAlternatingLift, alternatingInner, hdiv]

theorem terminalAlternatingLift_right (ψ : Fin 10 → ℝ)
    (u : Fin 5 → Fin 10) (φ : Fin 5 → ℝ) (i : Fin 5) :
    terminalAlternatingLift ψ u φ (alternatingRight i) =
      if u i = Fin.last 9 then ψ 0 + 2 * Real.pi else ψ (u i + 1) := by
  have hdiv : (⟨(3 * i.val + 2) / 3, by omega⟩ : Fin 5) = i := by
    apply Fin.ext
    simp
    omega
  simp [terminalAlternatingLift, alternatingRight, hdiv]

theorem candidate_contactAngle_pos :
    0 < contactAngle candidateB candidateInnerRadius := by
  have hsin := candidate_contact_angle_cos_sin.2
  have hsinpos : 0 < 2 * Candidate.s / candidateB := by
    positivity [Candidate.s_pos, candidateB_pos]
  have hne : contactAngle candidateB candidateInnerRadius ≠ 0 := by
    intro h
    rw [h, Real.sin_zero] at hsin
    linarith
  have hnonneg : 0 ≤ contactAngle candidateB candidateInnerRadius := by
    unfold contactAngle
    exact Real.arccos_nonneg _
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem candidate_outerAlpha_pos : 0 < outerAlpha candidateB := by
  have hB : 1 ≤ candidateB := by
    linarith [candidateB_local_bounds.1]
  have h := outerAlpha_ge_two_div candidateB hB
  have hfrac : 0 < 2 / candidateB := by positivity
  exact lt_of_lt_of_le hfrac h

theorem terminalOuterAngle_strictMono
    (ψ : Fin 10 → ℝ) (u : Fin 5 → Fin 10)
    (hparity : ∃ a : Fin 2, ∀ i, (u i).val = a.val + 2 * i.val)
    (hempty : ∀ k, (∀ i, u i ≠ k) →
      cyclicAngleGap ψ k = outerAlpha candidateB)
    (hoccupied : ∀ i,
      cyclicAngleGap ψ (u i) = 2 * contactAngle candidateB candidateInnerRadius) :
    StrictMono ψ := by
  have hγ := candidate_contactAngle_pos
  have hα := candidate_outerAlpha_pos
  have hgap (k : Fin 10) (hk : k ≠ Fin.last 9) :
      0 < cyclicAngleGap ψ k := by
    by_cases hmem : ∃ i, u i = k
    · rcases hmem with ⟨i, rfl⟩
      rw [hoccupied]
      linarith
    · have he := hempty k (by
        intro i hik
        exact hmem ⟨i, hik⟩)
      rw [he]
      exact hα
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  have hknot : k.castSucc ≠ Fin.last 9 := by
    intro he
    have hv := congrArg Fin.val he
    simp at hv
    omega
  have hg := hgap k.castSucc hknot
  unfold cyclicAngleGap at hg
  have hknot9 : k.castSucc ≠ (9 : Fin 10) := by simpa [Fin.last] using hknot
  simp [hknot9] at hg
  exact hg

/-- The angle data from the terminal equality case, placed into the local
left, inner, right order, form a strictly increasing lift. The wraparound
case is handled by adding one full turn to the last outer direction. -/
theorem terminalAlternatingLift_strictMono
    (ψ : Fin 10 → ℝ) (u : Fin 5 → Fin 10) (φ : Fin 5 → ℝ)
    (hparity : ∃ a : Fin 2, ∀ i, (u i).val = a.val + 2 * i.val)
    (hphase : ∀ i, φ i = ψ (u i) + contactAngle candidateB candidateInnerRadius)
    (hempty : ∀ k, (∀ i, u i ≠ k) →
      cyclicAngleGap ψ k = outerAlpha candidateB)
    (hoccupied : ∀ i,
      cyclicAngleGap ψ (u i) = 2 * contactAngle candidateB candidateInnerRadius) :
    StrictMono (terminalAlternatingLift ψ u φ) := by
  have hγ := candidate_contactAngle_pos
  have hα := candidate_outerAlpha_pos
  have hleftinner (i : Fin 5) :
      terminalAlternatingLift ψ u φ (alternatingLeft i) <
        terminalAlternatingLift ψ u φ (alternatingInner i) := by
    rw [terminalAlternatingLift_left, terminalAlternatingLift_inner]
    rw [hphase i]
    linarith
  have hinnerright (i : Fin 5) :
      terminalAlternatingLift ψ u φ (alternatingInner i) <
        terminalAlternatingLift ψ u φ (alternatingRight i) := by
    rw [terminalAlternatingLift_inner, terminalAlternatingLift_right]
    by_cases hlast : u i = Fin.last 9
    · have hlast9 : u i = (9 : Fin 10) := by simpa [Fin.last] using hlast
      have hg := hoccupied i
      unfold cyclicAngleGap at hg
      simp [hlast9] at hg
      have hp := hphase i
      rw [hlast9] at hp
      simp [hlast9]
      linarith
    · have hnot9 : u i ≠ (9 : Fin 10) := by simpa [Fin.last] using hlast
      have hg := hoccupied i
      unfold cyclicAngleGap at hg
      simp [hnot9] at hg
      have hp := hphase i
      simp [hnot9]
      linarith
  have hrightnext (i : Fin 5) (hi : i.val < 4) :
      terminalAlternatingLift ψ u φ (alternatingRight i) <
        terminalAlternatingLift ψ u φ (alternatingLeft (i + 1)) := by
    rw [terminalAlternatingLift_right, terminalAlternatingLift_left]
    rcases hparity with ⟨a, ha⟩
    have hu : (u i).val = a.val + 2 * i.val := ha i
    have hui1 : (u (i + 1)).val = a.val + 2 * (i + 1).val := ha (i + 1)
    have hnotLast : u i ≠ Fin.last 9 := by
      intro he
      have heval := congrArg Fin.val he
      simp [Fin.last] at heval
      omega
    have hnot9 : u i ≠ (9 : Fin 10) := by simpa [Fin.last] using hnotLast
    have hklt : (u i + 1).val < 9 := by
      simp [Fin.val_add]
      omega
    have hknotLast : u i + 1 ≠ Fin.last 9 := by
      intro he
      have heval := congrArg Fin.val he
      simp [Fin.val_add, Fin.last] at heval
      omega
    have hknot9 : u i + 1 ≠ (9 : Fin 10) := by simpa [Fin.last] using hknotLast
    have hnonmem : ∀ j, u j ≠ u i + 1 := by
      intro j he
      have heval := congrArg Fin.val he
      have hj := ha j
      simp [Fin.val_add] at heval
      omega
    have hg := hempty (u i + 1) hnonmem
    unfold cyclicAngleGap at hg
    simp [hknot9] at hg
    have hnext : u i + 2 = u (i + 1) := by
      apply Fin.ext
      simp [Fin.val_add]
      omega
    have hsucc : u i + 1 + 1 = u i + 2 := by
      apply Fin.ext
      simp [Fin.val_add]
    have hg' := hg
    rw [hsucc, hnext] at hg'
    simp [hnot9]
    linarith [hg', hα]
  have hstep : ∀ k : Fin 14,
      terminalAlternatingLift ψ u φ k.castSucc <
        terminalAlternatingLift ψ u φ k.succ := by
    intro k
    let i : Fin 5 := ⟨k.val / 3, by omega⟩
    have hmod : k.val % 3 = 0 ∨ k.val % 3 = 1 ∨ k.val % 3 = 2 := by omega
    rcases hmod with hmod | hmod | hmod
    · have hkleft : k.castSucc = alternatingLeft i := by
        apply Fin.ext
        simp [i, alternatingLeft]
        omega
      have hkinner : k.succ = alternatingInner i := by
        apply Fin.ext
        simp [i, alternatingInner]
        omega
      rw [hkleft, hkinner]
      exact hleftinner i
    · have hkinner : k.castSucc = alternatingInner i := by
        apply Fin.ext
        simp [i, alternatingInner]
        omega
      have hright : k.succ = alternatingRight i := by
        apply Fin.ext
        simp [i, alternatingRight]
        omega
      rw [hkinner, hright]
      exact hinnerright i
    · have hi : i.val < 4 := by
        dsimp [i]
        omega
      have hright : k.castSucc = alternatingRight i := by
        apply Fin.ext
        simp [i, alternatingRight]
        omega
      have hleft : k.succ = alternatingLeft (i + 1) := by
        apply Fin.ext
        simp [i, alternatingLeft, Fin.val_add]
        omega
      rw [hright, hleft]
      exact hrightnext i hi
  exact Fin.strictMono_iff_lt_succ.mpr hstep

theorem terminalAlternatingLift_span_lt_twoPi
    (ψ : Fin 10 → ℝ) (u : Fin 5 → Fin 10) (φ : Fin 5 → ℝ)
    (hparity : ∃ a : Fin 2, ∀ i, (u i).val = a.val + 2 * i.val)
    (hψmono : StrictMono ψ)
    (hwrap : ψ 9 < ψ 0 + 2 * Real.pi) :
    terminalAlternatingLift ψ u φ 14 -
      terminalAlternatingLift ψ u φ 0 < 2 * Real.pi := by
  rcases hparity with ⟨a, ha⟩
  have ha0 : a.val = 0 ∨ a.val = 1 := by omega
  rcases ha0 with hzero | hone
  · have hu0 : u 0 = (0 : Fin 10) := by
      apply Fin.ext
      have h := ha 0
      simp at h
      omega
    have hu4 : u 4 = (8 : Fin 10) := by
      apply Fin.ext
      have h := ha 4
      simp at h
      omega
    change terminalAlternatingLift ψ u φ (alternatingRight 4) -
      terminalAlternatingLift ψ u φ (alternatingLeft 0) < 2 * Real.pi
    rw [terminalAlternatingLift_right, terminalAlternatingLift_left]
    simp [hu0, hu4]
    linarith
  · have hu0 : u 0 = (1 : Fin 10) := by
      apply Fin.ext
      have h := ha 0
      simp at h
      omega
    have hu4 : u 4 = (9 : Fin 10) := by
      apply Fin.ext
      have h := ha 4
      simp at h
      omega
    change terminalAlternatingLift ψ u φ (alternatingRight 4) -
      terminalAlternatingLift ψ u φ (alternatingLeft 0) < 2 * Real.pi
    rw [terminalAlternatingLift_right, terminalAlternatingLift_left]
    have hmono01 := hψmono (show (0 : Fin 10) < 1 by norm_num)
    simp [hu0, hu4, Fin.last]
    linarith

end CP15
