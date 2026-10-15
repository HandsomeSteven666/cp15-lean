import CP15.Definitions

namespace CP15.Certificate

/-- Closed rational boxes include their endpoints. This is the domain
convention of the adaptive radius certificates. -/
structure ClosedBox (n : ℕ) where
  lower : Fin n → ℚ
  upper : Fin n → ℚ

def ClosedBox.Contains {n : ℕ} (box : ClosedBox n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (box.lower i : ℝ) ≤ x i ∧ x i ≤ (box.upper i : ℝ)

def ClosedBox.left {n : ℕ} (box : ClosedBox n) (i : Fin n) (cut : ℚ) :
    ClosedBox n := ⟨box.lower, Function.update box.upper i cut⟩

def ClosedBox.right {n : ℕ} (box : ClosedBox n) (i : Fin n) (cut : ℚ) :
    ClosedBox n := ⟨Function.update box.lower i cut, box.upper⟩

/-- Every parent point is in at least one closed child. Points on the
splitting hyperplane are in both children and can never be dropped. -/
theorem closed_split_covers {n : ℕ} (box : ClosedBox n)
    (i : Fin n) (cut : ℚ) (x : Fin n → ℝ) (hx : box.Contains x) :
    (box.left i cut).Contains x ∨ (box.right i cut).Contains x := by
  by_cases h : x i ≤ (cut : ℝ)
  · left
    intro j
    by_cases hj : j = i
    · subst j
      exact ⟨(hx i).1, by simpa [ClosedBox.left] using h⟩
    · simpa [ClosedBox.left, hj] using hx j
  · right
    intro j
    by_cases hj : j = i
    · subst j
      exact ⟨by simpa [ClosedBox.right] using (le_of_not_ge h), (hx i).2⟩
    · simpa [ClosedBox.right, hj] using hx j

/-- A finite subdivision certificate. Leaves may be impossible boxes or
boxes discharged by a separately proved analytic local lemma. -/
inductive BoxCover {n : ℕ} (leaf : ClosedBox n → Prop) : ClosedBox n → Prop
  | finish {box} : leaf box → BoxCover leaf box
  | split {box} (i : Fin n) (cut : ℚ) :
      BoxCover leaf (box.left i cut) →
      BoxCover leaf (box.right i cut) → BoxCover leaf box

/-- Soundness is independent of how the subdivision was found. It needs
a mathematical implication for every leaf, not an external success flag. -/
theorem BoxCover.sound {n : ℕ} {leaf : ClosedBox n → Prop}
    {root : ClosedBox n} (cover : BoxCover leaf root)
    (goal : (Fin n → ℝ) → Prop)
    (hleaf : ∀ box, leaf box → ∀ x, box.Contains x → goal x) :
    ∀ x, root.Contains x → goal x := by
  induction cover with
  | finish h => exact hleaf _ h
  | @split box i cut _ _ ihl ihr =>
      intro x hx
      rcases closed_split_covers box i cut x hx with hl | hr
      · exact ihl x hl
      · exact ihr x hr

end CP15.Certificate
