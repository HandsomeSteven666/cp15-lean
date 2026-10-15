import CP15.K10ModelEdge
import CP15.ExpandedLocalClosed

namespace CP15

set_option maxHeartbeats 0

def k10CachedBox (box : Certificate.ClosedBox 5) : Certificate.ClosedBox 5 :=
  ⟨fun i => (Vector.ofFn box.lower)[i], fun i => (Vector.ofFn box.upper)[i]⟩

theorem k10CachedBox_eq (box : Certificate.ClosedBox 5) : k10CachedBox box = box := by
  cases box
  simp [k10CachedBox]

inductive K10ModelCover where
  | outer (gamma : Fin 5 → Fin 79)
  | inner (pair : Fin 5 → Fin 736)
  | cycle (start : Fin 5) (edges : List K10TableEdge)
  | local
  | split (i : Fin 5) (cut : ℚ) (left right : K10ModelCover)

def k10ModelCoverCheck (empty : Fin 5 → ℕ) (alpha turn : ℕ) :
    Certificate.ClosedBox 5 → K10ModelCover → Bool
  | box, .outer gamma => decide (∀ i, k10GammaMatches box i (gamma i) = true) &&
      decide (turn < 5 * alpha + ∑ i, max alpha (2 * (k10GammaEntry (gamma i)).units))
  | box, .inner pair => decide (∀ i, k10PairMatches box i (i + 1) (pair i) = true) &&
      decide (turn < ∑ i, (k10PairEntry (pair i)).units)
  | box, .cycle start edges => edges.all (fun edge => edge.matches box) &&
      Certificate.positiveCycleCheck (edges.map (fun edge => edge.differenceEdge empty alpha turn)) start
  | box, .local => decide (∀ i, empty i = 1 ∧ (42 / 25 : ℚ) ≤ box.lower i ∧ box.upper i ≤ 43 / 25)
  | box, .split i cut left right =>
      k10ModelCoverCheck empty alpha turn (k10CachedBox (box.left i cut)) left &&
        k10ModelCoverCheck empty alpha turn (k10CachedBox (box.right i cut)) right

/-- Opaque combination keeps exact leaf checking separate from the
complete tree's conversion check. Both closed children are retained. -/
theorem k10ModelCoverCheck_split_true (empty : Fin 5 → ℕ) (alpha turn : ℕ)
    (box : Certificate.ClosedBox 5) (i : Fin 5) (cut : ℚ) (left right : K10ModelCover)
    (hl : k10ModelCoverCheck empty alpha turn (k10CachedBox (box.left i cut)) left = true)
    (hr : k10ModelCoverCheck empty alpha turn (k10CachedBox (box.right i cut)) right = true) :
    k10ModelCoverCheck empty alpha turn box (.split i cut left right) = true := by
  simp only [k10ModelCoverCheck, Bool.and_eq_true]
  exact ⟨hl, hr⟩

/-- Full semantic soundness: numerical entries have already been proved
as real angular lower bounds; every leaf checks its box, edges, wrap,
positive weight, or membership in the proved analytic cube. -/
theorem k10ModelCoverCheck_equality (empty : Fin 5 → ℕ) (alpha turn : ℕ)
    (box : Certificate.ClosedBox 5) (cover : K10ModelCover)
    (hc : k10ModelCoverCheck empty alpha turn box cover = true)
    (b : ℝ) (r g : Fin 5 → ℝ) (hb : 3 < b) (hbC : b ≤ candidateB)
    (h : CyclicInnerModel b r empty g) (hx : box.Contains r)
    (hα : (alpha : ℝ) ≤ 100000 * outerAlpha b)
    (hαβ : (alpha : ℝ) ≤ 100000 * (57588 / 100000 : ℝ))
    (hturn : 100000 * (2 * Real.pi) ≤ turn) :
    b = candidateB ∧ empty = (fun _ => 1) ∧
      (∀ i, r i = candidateInnerRadius) := by
  have hbB : b ≤ (3521357 / 1000000 : ℝ) :=
    hbC.trans Candidate.candidateB_lt_3521357_div_1000000.le
  induction cover generalizing box with
  | outer gamma =>
      have hd : (∀ i, k10GammaMatches box i (gamma i) = true) ∧
          turn < 5 * alpha + ∑ i, max alpha (2 * (k10GammaEntry (gamma i)).units) := by
        simpa [k10ModelCoverCheck] using hc
      have hm (i : Fin 5) : ((max alpha (2 * (k10GammaEntry (gamma i)).units) : ℕ) : ℝ) ≤
          100000 * max (57588 / 100000 : ℝ) (2 * contactAngle b (r i)) := by
        have hg := k10GammaMatches_lower box i (gamma i) b r hb hbB
          (fun i => (h.radius i).2) hx (hd.1 i)
        have hl := le_max_left (57588 / 100000 : ℝ) (2 * contactAngle b (r i))
        have hr := le_max_right (57588 / 100000 : ℝ) (2 * contactAngle b (r i))
        rw [Nat.cast_max, Nat.cast_mul, Nat.cast_ofNat]
        apply max_le <;> nlinarith
      have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hm i)
      have hs' : ((∑ i, max alpha (2 * (k10GammaEntry (gamma i)).units) : ℕ) : ℝ) ≤
          100000 * (∑ i, max (57588 / 100000 : ℝ) (2 * contactAngle b (r i))) := by
        simpa [Nat.cast_sum, ← Finset.mul_sum] using hs
      have hn : (turn : ℝ) < 5 * (alpha : ℝ) +
          ((∑ i, max alpha (2 * (k10GammaEntry (gamma i)).units) : ℕ) : ℝ) := by
        exact_mod_cast hd.2
      exact False.elim (by nlinarith [h.outer_cost])
  | inner pair =>
      have hd : (∀ i, k10PairMatches box i (i + 1) (pair i) = true) ∧
          turn < ∑ i, (k10PairEntry (pair i)).units := by
        simpa [k10ModelCoverCheck] using hc
      have hm (i : Fin 5) : ((k10PairEntry (pair i)).units : ℝ) ≤ 100000 * g i := by
        have hp := k10PairMatches_lower box i (i + 1) (pair i) r
          (fun i => (h.radius i).1) hx (hd.1 i)
        have hh := h.pair i 1 (by decide)
        norm_num [fiveArc] at hh
        linarith
      have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hm i)
      have hs' : ((∑ i, (k10PairEntry (pair i)).units : ℕ) : ℝ) ≤
          100000 * (2 * Real.pi) := by
        simpa [Nat.cast_sum, ← Finset.mul_sum, h.gap_sum] using hs
      have hn : (turn : ℝ) < ((∑ i, (k10PairEntry (pair i)).units : ℕ) : ℝ) := by
        exact_mod_cast hd.2
      exact False.elim (by linarith)
  | cycle start edges =>
      have hd : edges.all (fun edge => edge.matches box) = true ∧
          Certificate.positiveCycleCheck
            (edges.map (fun edge => edge.differenceEdge empty alpha turn)) start = true := by
        simpa [k10ModelCoverCheck] using hc
      have hm : ∀ edge ∈ edges, edge.matches box = true := by
        simpa only [List.all_eq_true] using hd.1
      apply False.elim
      apply Certificate.positive_cycle_impossible
        (edges.map (fun edge => edge.differenceEdge empty alpha turn))
        (edges.map (fun edge => edge.differenceEdge empty alpha turn)) start
        (fun i => 100000 * fiveArc g 0 i) 1 (by norm_num) hd.2 (fun _ hh => hh)
      intro edge he
      obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp he
      simpa [K10TableEdge.differenceEdge] using raw.difference_bound box b r empty g alpha turn hb hbB h hx hα hturn (hm raw hr)
  | «local» =>
      have hd : ∀ i, empty i = 1 ∧ (42 / 25 : ℚ) ≤ box.lower i ∧ box.upper i ≤ 43 / 25 := by
        simpa [k10ModelCoverCheck] using hc
      have heq : empty = (fun _ => 1) := funext (fun i => (hd i).1)
      have hr (i : Fin 5) : r i ∈ Set.Icc (42 / 25 : ℝ) (43 / 25) := by
        have hl0 : ((42 / 25 : ℚ) : ℝ) ≤ box.lower i := by exact_mod_cast (hd i).2.1
        have hu0 : (box.upper i : ℝ) ≤ ((43 / 25 : ℚ) : ℝ) := by exact_mod_cast (hd i).2.2
        have hl : (42 / 25 : ℝ) ≤ box.lower i := by simpa using hl0
        have hu : (box.upper i : ℝ) ≤ 43 / 25 := by simpa using hu0
        exact ⟨hl.trans (hx i).1, (hx i).2.trans hu⟩
      rw [heq] at h
      have hh := expanded_local_angle_budget_closed b r hb hbC hr h.alternating_cost
      exact ⟨hh.1, heq, hh.2⟩
  | split i cut left right ihl ihr =>
      have hd : k10ModelCoverCheck empty alpha turn (box.left i cut) left = true ∧
          k10ModelCoverCheck empty alpha turn (box.right i cut) right = true := by
        simpa only [k10ModelCoverCheck, k10CachedBox_eq, Bool.and_eq_true] using hc
      rcases Certificate.closed_split_covers box i cut r hx with hl | hr
      · exact ihl _ hd.1 hl
      · exact ihr _ hd.2 hr

/-- The value bound used by the main proof is a consequence of the stronger
equality certificate.  The latter also identifies the sole surviving
occupancy word and all five inner radii at the endpoint. -/
theorem k10ModelCoverCheck_sound (empty : Fin 5 → ℕ) (alpha turn : ℕ)
    (box : Certificate.ClosedBox 5) (cover : K10ModelCover)
    (hc : k10ModelCoverCheck empty alpha turn box cover = true)
    (b : ℝ) (r g : Fin 5 → ℝ) (hb : 3 < b) (hbC : b ≤ candidateB)
    (h : CyclicInnerModel b r empty g) (hx : box.Contains r)
    (hα : (alpha : ℝ) ≤ 100000 * outerAlpha b)
    (hαβ : (alpha : ℝ) ≤ 100000 * (57588 / 100000 : ℝ))
    (hturn : 100000 * (2 * Real.pi) ≤ turn) : candidateB ≤ b := by
  exact (k10ModelCoverCheck_equality empty alpha turn box cover hc b r g
    hb hbC h hx hα hαβ hturn).1.ge

end CP15
