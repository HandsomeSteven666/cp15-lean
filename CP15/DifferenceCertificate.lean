import CP15.Definitions

namespace CP15.Certificate

/-- A directed lower bound: `weight * unit ≤ angle dst - angle src`.
Integer arithmetic is exact; no floating-point or external checker result
is used in the soundness theorem. -/
structure DifferenceEdge (n : ℕ) where
  src : Fin n
  dst : Fin n
  weight : ℤ
  deriving DecidableEq, Repr

def walkCheck {n : ℕ} : List (DifferenceEdge n) → Fin n → Fin n → Bool
  | [], u, v => decide (u = v)
  | e :: rest, u, v => decide (e.src = u) && walkCheck rest e.dst v

def walkWeight {n : ℕ} : List (DifferenceEdge n) → ℤ
  | [] => 0
  | e :: rest => e.weight + walkWeight rest

def positiveCycleCheck {n : ℕ} (edges : List (DifferenceEdge n))
    (start : Fin n) : Bool :=
  walkCheck edges start start && decide (0 < walkWeight edges)

/-- Every checked walk telescopes. This theorem proves the bridge from
the finite integer certificate to real angular inequalities. -/
theorem checked_walk_bound {n : ℕ}
    (edges : List (DifferenceEdge n)) (u v : Fin n)
    (angle : Fin n → ℝ) (unit : ℝ)
    (hwalk : walkCheck edges u v = true)
    (hbound : ∀ e ∈ edges,
      (e.weight : ℝ) * unit ≤ angle e.dst - angle e.src) :
    (walkWeight edges : ℝ) * unit ≤ angle v - angle u := by
  induction edges generalizing u with
  | nil =>
      have huv : u = v := by simpa [walkCheck] using hwalk
      simp [walkWeight, huv]
  | cons e rest ih =>
      have hw : e.src = u ∧ walkCheck rest e.dst v = true := by
        simpa only [walkCheck, Bool.and_eq_true, decide_eq_true_eq] using hwalk
      have he := hbound e (by simp)
      have hr := ih e.dst hw.2 (fun f hf => hbound f (by simp [hf]))
      simp only [walkWeight, Int.cast_add]
      rw [hw.1] at he
      nlinarith

/-- A positive closed walk contradicts every real solution of its edge
bounds. Membership of every cycle edge in the supplied graph is checked
separately, so a generator cannot invent an additional constraint. -/
theorem positive_cycle_impossible {n : ℕ}
    (graph cycle : List (DifferenceEdge n)) (start : Fin n)
    (angle : Fin n → ℝ) (unit : ℝ)
    (hunit : 0 < unit)
    (hcheck : positiveCycleCheck cycle start = true)
    (hmembership : ∀ e ∈ cycle, e ∈ graph)
    (hgraph : ∀ e ∈ graph,
      (e.weight : ℝ) * unit ≤ angle e.dst - angle e.src) : False := by
  have hc : walkCheck cycle start start = true ∧ 0 < walkWeight cycle := by
    simpa only [positiveCycleCheck, Bool.and_eq_true, decide_eq_true_eq] using hcheck
  have hb := checked_walk_bound cycle start start angle unit hc.1
    (fun e he => hgraph e (hmembership e he))
  have hw : (0 : ℝ) < (walkWeight cycle : ℝ) := by exact_mod_cast hc.2
  have hp := mul_pos hw hunit
  simp only [sub_self] at hb
  linarith

/-- A rationally rounded upper bound on one turn makes a wrapped lower
bound weaker, hence valid. The sign of this rounding is part of the proof. -/
theorem wrapped_edge_bound (a b δ turn upper : ℝ)
    (hupper : turn ≤ upper) (hgap : δ ≤ b + turn - a) :
    δ - upper ≤ b - a := by
  linarith

/-- Division-free scaling of a certified integer lower bound. -/
theorem integer_angle_lower (k : ℤ) (unit value : ℝ)
    (hunit : 0 < unit) (h : (k : ℝ) * unit < value) :
    (k : ℝ) ≤ value / unit := by
  exact (le_div_iff₀ hunit).2 h.le

-- Kernel-evaluated regression examples: positive, zero, and open walks.
example : positiveCycleCheck
    [⟨(0 : Fin 2), 1, 3⟩, ⟨1, 0, -2⟩] 0 = true := by decide
example : positiveCycleCheck
    [⟨(0 : Fin 2), 1, 2⟩, ⟨1, 0, -2⟩] 0 = false := by decide
example : positiveCycleCheck
    [⟨(0 : Fin 2), 1, 3⟩] 0 = false := by decide

end CP15.Certificate
