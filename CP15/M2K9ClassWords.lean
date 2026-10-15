import CP15.M2TangentialSelection

namespace CP15

/-- The three radius classes in the distinct-blocker six-center order. -/
inductive M2Kind | A | H | L deriving DecidableEq

def classCount (w : Fin 6 → M2Kind) (k : M2Kind) : ℕ :=
  (Finset.univ.filter (fun i => w i = k)).card

/-- Angle lower bounds in tenths of a degree. The strict geometric
inequalities are separate premises when this finite theorem is used. -/
def classGapCost : M2Kind → M2Kind → ℕ
  | .A, .A => 1000
  | .A, .H | .H, .A => 490
  | .A, .L | .L, .A => 708
  | .H, .H => 490
  | .H, .L | .L, .H => 530
  | .L, .L => 600

def classBudget (w : Fin 6 → M2Kind) : ℕ :=
  ∑ i : Fin 6, classGapCost (w i) (w (i + 1))

def cyclicNeighbor (i j : Fin 6) : Prop :=
  j = i + 1 ∨ i = j + 1

def matchedAdjacentHighs (w : Fin 6 → M2Kind) : Prop :=
  ∃ a₁ a₂ h₁ h₂ : Fin 6,
    a₁ ≠ a₂ ∧ h₁ ≠ h₂ ∧
    w a₁ = .A ∧ w a₂ = .A ∧
    w h₁ = .H ∧ w h₂ = .H ∧
    cyclicNeighbor a₁ h₁ ∧ cyclicNeighbor a₂ h₂

private instance (w : Fin 6 → M2Kind) :
    Decidable (matchedAdjacentHighs w) := by
  unfold matchedAdjacentHighs cyclicNeighbor
  infer_instance

def dihedralEquivalent
    (w z : Fin 6 → M2Kind) : Prop :=
  ∃ k : Fin 6,
    (∀ i, w i = z (i + k)) ∨
      (∀ i, w i = z (k - i))

private instance (w z : Fin 6 → M2Kind) :
    Decidable (dihedralEquivalent w z) := by
  unfold dihedralEquivalent
  infer_instance

def wordAHAHLL : Fin 6 → M2Kind :=
  ![.A, .H, .A, .H, .L, .L]
def wordAHALHL : Fin 6 → M2Kind :=
  ![.A, .H, .A, .L, .H, .L]
def wordAHHALL : Fin 6 → M2Kind :=
  ![.A, .H, .H, .A, .L, .L]
def wordAHLAHL : Fin 6 → M2Kind :=
  ![.A, .H, .L, .A, .H, .L]
def wordAHLHAL : Fin 6 → M2Kind :=
  ![.A, .H, .L, .H, .A, .L]

/-- Both low centers and one high center flank each core center. The
separate geometric two-gap estimate excludes this predicate. -/
def bothCoreHighLow (w : Fin 6 → M2Kind) : Prop :=
  ∀ a : Fin 6, w a = .A →
    (w (a + 1) = .H ∧ w (a - 1) = .L) ∨
    (w (a + 1) = .L ∧ w (a - 1) = .H)

private instance (w : Fin 6 → M2Kind) :
    Decidable (bothCoreHighLow w) := by
  unfold bothCoreHighLow
  infer_instance

/-- Exhaustive finite class-word calculation only. It assumes the six
class counts, the certified class-angle lower costs, and a distinct
adjacent blocker matching; it asserts nothing about contact graphs. -/
theorem distinct_class_word_four_orbits
    (w : Fin 6 → M2Kind)
    (hA : classCount w .A = 2)
    (hH : classCount w .H = 2)
    (hL : classCount w .L = 2)
    (hbudget : classBudget w ≤ 3600)
    (hmatch : matchedAdjacentHighs w) :
    dihedralEquivalent w wordAHAHLL ∨
    dihedralEquivalent w wordAHHALL ∨
    dihedralEquivalent w wordAHLAHL ∨
    dihedralEquivalent w wordAHLHAL := by
  have hw : w = ![w 0, w 1, w 2, w 3, w 4, w 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hw] at hA hH hL hbudget hmatch ⊢
  revert hA hH hL hbudget hmatch
  cases h0 : w 0 <;> cases h1 : w 1 <;>
    cases h2 : w 2 <;> cases h3 : w 3 <;>
    cases h4 : w 4 <;> cases h5 : w 5 <;>
    decide

/-- Conditional final class word. The only additional premise is the
geometric exclusion of the two-gap high/low pattern at both cores. -/
theorem distinct_class_word_single_orbit
    (w : Fin 6 → M2Kind)
    (hA : classCount w .A = 2)
    (hH : classCount w .H = 2)
    (hL : classCount w .L = 2)
    (hbudget : classBudget w ≤ 3600)
    (hmatch : matchedAdjacentHighs w)
    (hHL : ¬bothCoreHighLow w) :
    dihedralEquivalent w wordAHAHLL := by
  have hw : w = ![w 0, w 1, w 2, w 3, w 4, w 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hw] at hA hH hL hbudget hmatch hHL ⊢
  revert hA hH hL hbudget hmatch hHL
  cases h0 : w 0 <;> cases h1 : w 1 <;>
    cases h2 : w 2 <;> cases h3 : w 3 <;>
    cases h4 : w 4 <;> cases h5 : w 5 <;>
    decide

/-- The local flanking condition has only three cyclic six-letter words
when each of A, H, and L occurs twice. This is a finite class-word fact;
it makes no geometric or graph-completeness assertion. -/
theorem bothCore_class_words
    (w : Fin 6 → M2Kind)
    (hA : classCount w .A = 2)
    (hH : classCount w .H = 2)
    (hL : classCount w .L = 2)
    (hflank : bothCoreHighLow w) :
    dihedralEquivalent w wordAHALHL ∨
      dihedralEquivalent w wordAHHALL ∨
      dihedralEquivalent w wordAHLAHL ∨
      dihedralEquivalent w wordAHLHAL := by
  have hw : w = ![w 0, w 1, w 2, w 3, w 4, w 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hw] at hA hH hL hflank ⊢
  revert hA hH hL hflank
  cases h0 : w 0 <;> cases h1 : w 1 <;>
    cases h2 : w 2 <;> cases h3 : w 3 <;>
    cases h4 : w 4 <;> cases h5 : w 5 <;>
    decide

/-- Coarse class costs for the shared blocker when all three other
touching inner centers have radius at most two. Units are tenths of a
degree. The `AH=49.2°` and `AL=70.8°` thresholds sum to `120°`. -/
def sharedAllLowCost : M2Kind → M2Kind → ℕ
  | .A, .A => 990
  | .A, .H | .H, .A => 492
  | .A, .L | .L, .A => 708
  | .H, .H => 0
  | .H, .L | .L, .H => 530
  | .L, .L => 600

def sharedAllLowBudget (w : Fin 6 → M2Kind) : ℕ :=
  ∑ i : Fin 6, sharedAllLowCost (w i) (w (i + 1))

/-- Exhaustive six-letter class budget. No symmetry quotient is assumed:
all `3^6` words are reduced by the kernel. -/
theorem shared_all_other_touching_low_cost_ge_full_turn
    (w : Fin 6 → M2Kind)
    (hA : classCount w .A = 2)
    (hH : classCount w .H = 1)
    (hL : classCount w .L = 3) :
    3600 ≤ sharedAllLowBudget w := by
  have hw : w = ![w 0, w 1, w 2, w 3, w 4, w 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hw] at hA hH hL ⊢
  revert hA hH hL
  cases h0 : w 0 <;> cases h1 : w 1 <;>
    cases h2 : w 2 <;> cases h3 : w 3 <;>
    cases h4 : w 4 <;> cases h5 : w 5 <;>
    decide

end CP15
