import CP15.K10AngleTables
import CP15.CyclicInnerModel
import CP15.ClosedBoxCertificate

namespace CP15

set_option maxHeartbeats 0

def k10GammaMatches (box : Certificate.ClosedBox 5) (i : Fin 5) (a : Fin 79) : Bool :=
  decide ((k10GammaEntry a).radius ≤ box.lower i)

def k10PairMatches (box : Certificate.ClosedBox 5) (i j : Fin 5) (a : Fin 736) : Bool :=
  decide ((box.upper i ≤ (k10PairEntry a).first ∧ box.upper j ≤ (k10PairEntry a).second) ∨
    (box.upper i ≤ (k10PairEntry a).second ∧ box.upper j ≤ (k10PairEntry a).first))

theorem k10GammaMatches_lower (box : Certificate.ClosedBox 5) (i : Fin 5) (a : Fin 79)
    (b : ℝ) (r : Fin 5 → ℝ) (hb : 3 < b) (hbB : b ≤ 3521357 / 1000000)
    (hr : ∀ i, r i ≤ 9 / 4) (hx : box.Contains r) (hc : k10GammaMatches box i a = true) :
    ((k10GammaEntry a).units : ℝ) / 100000 ≤ contactAngle b (r i) := by
  have hm : (k10GammaEntry a).radius ≤ box.lower i := by simpa [k10GammaMatches] using hc
  have hm' : ((k10GammaEntry a).radius : ℝ) ≤ box.lower i := by exact_mod_cast hm
  exact k10_gamma_entry_lower a b (r i) hb hbB (hm'.trans (hx i).1) (hr i)

theorem k10PairMatches_lower (box : Certificate.ClosedBox 5) (i j : Fin 5) (a : Fin 736)
    (r : Fin 5 → ℝ) (hr : ∀ i, (123 / 100 : ℝ) ≤ r i) (hx : box.Contains r)
    (hc : k10PairMatches box i j a = true) :
    ((k10PairEntry a).units : ℝ) / 100000 ≤ contactAngle (r i) (r j) := by
  have hm : (box.upper i ≤ (k10PairEntry a).first ∧ box.upper j ≤ (k10PairEntry a).second) ∨
      (box.upper i ≤ (k10PairEntry a).second ∧ box.upper j ≤ (k10PairEntry a).first) := by
    simpa [k10PairMatches] using hc
  rcases hm with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hi' : (box.upper i : ℝ) ≤ (k10PairEntry a).first := by exact_mod_cast hi
    have hj' : (box.upper j : ℝ) ≤ (k10PairEntry a).second := by exact_mod_cast hj
    exact k10_pair_entry_lower a (r i) (r j) (hr i) (hr j)
      ((hx i).2.trans hi') ((hx j).2.trans hj')
  · have hi' : (box.upper i : ℝ) ≤ (k10PairEntry a).second := by exact_mod_cast hi
    have hj' : (box.upper j : ℝ) ≤ (k10PairEntry a).first := by exact_mod_cast hj
    rw [contactAngle_comm]
    exact k10_pair_entry_lower a (r j) (r i) (hr j) (hr i)
      ((hx j).2.trans hj') ((hx i).2.trans hi')

inductive K10TableEdge where
  | pair (src dst : Fin 5) (entry : Fin 736)
  | support (src dst : Fin 5) (first second : Fin 79)

def K10TableEdge.src : K10TableEdge → Fin 5
  | .pair i _ _ => i
  | .support i _ _ _ => i

def K10TableEdge.dst : K10TableEdge → Fin 5
  | .pair _ j _ => j
  | .support _ j _ _ => j

def K10TableEdge.matches (box : Certificate.ClosedBox 5) : K10TableEdge → Bool
  | .pair i j a => decide (i ≠ j) && k10PairMatches box i j a
  | .support i j a c => decide (i ≠ j) && k10GammaMatches box i a && k10GammaMatches box j c

def K10TableEdge.rawWeight (empty : Fin 5 → ℕ) (alpha : ℕ) : K10TableEdge → ℕ
  | .pair _ _ a => (k10PairEntry a).units
  | .support i j a c => (k10GammaEntry a).units + (k10GammaEntry c).units +
      (fiveArc empty i (j - i) + (j - i).val - 1) * alpha

def K10TableEdge.differenceEdge (empty : Fin 5 → ℕ) (alpha turn : ℕ)
    (edge : K10TableEdge) : Certificate.DifferenceEdge 5 :=
  ⟨edge.src, edge.dst, (edge.rawWeight empty alpha : ℤ) -
    if edge.dst < edge.src then (turn : ℤ) else 0⟩

theorem finFive_difference_ne_zero : ∀ i j : Fin 5, i ≠ j → j - i ≠ 0 := by
  decide +kernel

theorem K10TableEdge.rawWeight_bound (box : Certificate.ClosedBox 5)
    (edge : K10TableEdge) (b : ℝ) (r : Fin 5 → ℝ) (empty : Fin 5 → ℕ)
    (g : Fin 5 → ℝ) (alpha : ℕ) (hb : 3 < b) (hbB : b ≤ 3521357 / 1000000)
    (h : CyclicInnerModel b r empty g) (hx : box.Contains r)
    (hα : (alpha : ℝ) ≤ 100000 * outerAlpha b) (hc : edge.matches box = true) :
    (edge.rawWeight empty alpha : ℝ) ≤ 100000 * fiveArc g edge.src (edge.dst - edge.src) := by
  cases edge with
  | pair i j a =>
      have hd : i ≠ j ∧ k10PairMatches box i j a = true := by
        simpa [K10TableEdge.matches] using hc
      have hp := k10PairMatches_lower box i j a r (fun i => (h.radius i).1) hx hd.2
      have hm := h.pair i (j - i) (finFive_difference_ne_zero i j hd.1)
      have heq : i + (j - i) = j := by abel
      rw [heq] at hm
      change ((k10PairEntry a).units : ℝ) ≤ 100000 * fiveArc g i (j - i)
      linarith
  | support i j a c =>
      have hd : (i ≠ j ∧ k10GammaMatches box i a = true) ∧
          k10GammaMatches box j c = true := by
        simpa [K10TableEdge.matches, Bool.and_eq_true] using hc
      have hi := k10GammaMatches_lower box i a b r hb hbB (fun i => (h.radius i).2) hx hd.1.2
      have hj := k10GammaMatches_lower box j c b r hb hbB (fun i => (h.radius i).2) hx hd.2
      have hm := h.support i (j - i) (finFive_difference_ne_zero i j hd.1.1)
      have heq : i + (j - i) = j := by abel
      rw [heq] at hm
      let n : ℕ := fiveArc empty i (j - i) + (j - i).val - 1
      have hmul := mul_le_mul_of_nonneg_left hα (show (0 : ℝ) ≤ n by positivity)
      change ((k10GammaEntry a).units + (k10GammaEntry c).units + n * alpha : ℕ) ≤
        100000 * fiveArc g i (j - i)
      push_cast
      dsimp [n] at hmul
      nlinarith

theorem K10TableEdge.difference_bound (box : Certificate.ClosedBox 5)
    (edge : K10TableEdge) (b : ℝ) (r : Fin 5 → ℝ) (empty : Fin 5 → ℕ)
    (g : Fin 5 → ℝ) (alpha turn : ℕ) (hb : 3 < b) (hbB : b ≤ 3521357 / 1000000)
    (h : CyclicInnerModel b r empty g) (hx : box.Contains r)
    (hα : (alpha : ℝ) ≤ 100000 * outerAlpha b) (hturn : 100000 * (2 * Real.pi) ≤ turn)
    (hc : edge.matches box = true) :
    ((edge.differenceEdge empty alpha turn).weight : ℝ) ≤
      100000 * fiveArc g 0 edge.dst - 100000 * fiveArc g 0 edge.src := by
  have hne : edge.src ≠ edge.dst := by
    cases edge with
    | pair i j a =>
        have hd : i ≠ j ∧ k10PairMatches box i j a = true := by
          simpa [K10TableEdge.matches] using hc
        exact hd.1
    | support i j a c =>
        have hd : (i ≠ j ∧ k10GammaMatches box i a = true) ∧
            k10GammaMatches box j c = true := by
          simpa [K10TableEdge.matches, Bool.and_eq_true] using hc
        exact hd.1.1
  have hr := edge.rawWeight_bound box b r empty g alpha hb hbB h hx hα hc
  have heq := fiveArc_as_difference g edge.src edge.dst hne
  rw [h.gap_sum] at heq
  simp only [K10TableEdge.differenceEdge, Int.cast_sub]
  by_cases hlt : edge.dst < edge.src
  · rw [if_pos hlt] at heq ⊢
    simp only [Int.cast_natCast]
    linarith
  · rw [if_neg hlt] at heq ⊢
    simp only [Int.cast_natCast, Int.cast_zero, sub_zero] at *
    linarith

end CP15
