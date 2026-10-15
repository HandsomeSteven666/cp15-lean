import CP15.Definitions

namespace CP15.Certificate

/-- Exact directed cost along a finite path, including its final edge. -/
def pathCost {α : Type*} (pair : α → α → ℕ) : α → List α → α → ℕ
  | current, [], last => pair current last
  | current, next :: tail, last => pair current next + pathCost pair next tail last

/-- A finite exhaustive checker with a sound early stop when the first
budget is already exceeded. Its output is proved in the Lean kernel;
an external enumeration result is never a hypothesis. -/
def pathCheck {α : Type*} (alphabet : List α) (extra : α → ℕ)
    (pair : α → α → ℕ) (extraLimit angleLimit : ℕ) (last : α) :
    ℕ → α → ℕ → ℕ → Bool
  | 0, current, cost, angle =>
      decide (extraLimit < cost ∨ angleLimit < angle + pair current last)
  | n + 1, current, cost, angle =>
      if extraLimit < cost then true else
        alphabet.all (fun next => pathCheck alphabet extra pair extraLimit angleLimit last
          n next (cost + extra next) (angle + pair current next))

/-- Every word over the stated alphabet is covered. Pruning only removes
words whose nonnegative first cost has already exceeded its budget. -/
theorem pathCheck_sound {α : Type*} (alphabet : List α) (extra : α → ℕ)
    (pair : α → α → ℕ) (extraLimit angleLimit : ℕ) (last : α)
    (n : ℕ) (current : α) (cost angle : ℕ)
    (hcheck : pathCheck alphabet extra pair extraLimit angleLimit last n current cost angle = true)
    (tail : List α) (hlen : tail.length = n) (hmem : ∀ x ∈ tail, x ∈ alphabet) :
    extraLimit < cost + (tail.map extra).sum ∨
      angleLimit < angle + pathCost pair current tail last := by
  induction n generalizing current cost angle tail with
  | zero =>
      have ht : tail = [] := List.eq_nil_of_length_eq_zero hlen
      subst tail
      simpa [pathCheck, pathCost] using hcheck
  | succ n ih =>
      cases tail with
      | nil => simp at hlen
      | cons next tail =>
          have hlen' : tail.length = n := by simpa using hlen
          by_cases hstop : extraLimit < cost
          · left
            simp only [List.map_cons, List.sum_cons]
            omega
          · have hall := hcheck
            simp only [pathCheck, if_neg hstop, List.all_eq_true] at hall
            have hnext := hall next (hmem next (by simp))
            have htail : ∀ x ∈ tail, x ∈ alphabet := fun x hx => hmem x (by simp [hx])
            have hs := ih next (cost + extra next) (angle + pair current next)
              hnext tail hlen' htail
            simpa only [List.map_cons, List.sum_cons, pathCost, Nat.add_assoc] using hs

end CP15.Certificate
