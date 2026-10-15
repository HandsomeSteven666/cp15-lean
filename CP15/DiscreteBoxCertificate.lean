import CP15.DifferenceCertificate

namespace CP15.Certificate

set_option maxHeartbeats 0

def natListMin (xs : List ℕ) : ℕ := xs.foldr min 70000

theorem natListMin_le_of_mem (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    natListMin xs ≤ x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih hx)

def intervalMin (f : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  natListMin ((List.range (hi + 1 - lo)).map (fun k => f (lo + k)))

theorem intervalMin_le (f : ℕ → ℕ) (lo hi x : ℕ) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    intervalMin f lo hi ≤ f x := by
  apply natListMin_le_of_mem
  apply List.mem_map.mpr
  refine ⟨x - lo, List.mem_range.mpr (by omega), ?_⟩
  congr 1
  omega

structure DiscreteBox (n : ℕ) where
  lower : Fin n → ℕ
  upper : Fin n → ℕ

def DiscreteBox.Contains {n : ℕ} (box : DiscreteBox n) (w : Fin n → ℕ) : Prop :=
  ∀ i, box.lower i ≤ w i ∧ w i ≤ box.upper i

def DiscreteBox.left {n : ℕ} (box : DiscreteBox n) (i : Fin n) (cut : ℕ) :
    DiscreteBox n := ⟨box.lower, Function.update box.upper i cut⟩

def DiscreteBox.right {n : ℕ} (box : DiscreteBox n) (i : Fin n) (cut : ℕ) :
    DiscreteBox n := ⟨Function.update box.lower i (cut + 1), box.upper⟩

/-- Materialize every finite bound after a split. This avoids retaining
long chains of updates during exact kernel evaluation. -/
def DiscreteBox.cached {n : ℕ} (box : DiscreteBox n) : DiscreteBox n :=
  ⟨fun i => (Vector.ofFn box.lower)[i], fun i => (Vector.ofFn box.upper)[i]⟩

theorem DiscreteBox.cached_eq {n : ℕ} (box : DiscreteBox n) : box.cached = box := by
  cases box
  simp [DiscreteBox.cached]

theorem discrete_split_covers {n : ℕ} (box : DiscreteBox n) (i : Fin n)
    (cut : ℕ) (w : Fin n → ℕ) (hw : box.Contains w) :
    (box.left i cut).Contains w ∨ (box.right i cut).Contains w := by
  by_cases h : w i ≤ cut
  · left
    intro j
    by_cases hj : j = i
    · subst j
      exact ⟨(hw i).1, by simpa [DiscreteBox.left] using h⟩
    · simpa [DiscreteBox.left, hj] using hw j
  · right
    intro j
    by_cases hj : j = i
    · subst j
      exact ⟨by simpa [DiscreteBox.right] using (show cut + 1 ≤ w i by omega), (hw i).2⟩
    · simpa [DiscreteBox.right, hj] using hw j

def boxExtraLower {n : ℕ} (extra : Fin n → ℕ → ℕ) (box : DiscreteBox n) : ℕ :=
  ∑ i, intervalMin (extra i) (box.lower i) (box.upper i)

def boxPairLower {n : ℕ} (pair : Fin n → Fin n → ℕ → ℕ → ℕ)
    (box : DiscreteBox n) (i j : Fin n) : ℕ :=
  intervalMin (fun x => intervalMin (pair i j x) (box.lower j) (box.upper j))
    (box.lower i) (box.upper i)

theorem boxExtraLower_le {n : ℕ} (extra : Fin n → ℕ → ℕ) (box : DiscreteBox n)
    (w : Fin n → ℕ) (hw : box.Contains w) :
    boxExtraLower extra box ≤ ∑ i, extra i (w i) :=
  Finset.sum_le_sum (fun i _ => intervalMin_le _ _ _ _ (hw i).1 (hw i).2)

theorem boxPairLower_le {n : ℕ} (pair : Fin n → Fin n → ℕ → ℕ → ℕ)
    (box : DiscreteBox n) (w : Fin n → ℕ) (hw : box.Contains w) (i j : Fin n) :
    boxPairLower pair box i j ≤ pair i j (w i) (w j) :=
  (intervalMin_le _ _ _ _ (hw i).1 (hw i).2).trans
    (intervalMin_le _ _ _ _ (hw j).1 (hw j).2)

def boxEdgeWeight {n : ℕ} (pair : Fin n → Fin n → ℕ → ℕ → ℕ)
    (turn : ℕ) (box : DiscreteBox n) (i j : Fin n) : ℤ :=
  if i < j then boxPairLower pair box i j
  else if j < i then (boxPairLower pair box j i : ℤ) - turn else 0

def boxCycleEdges {n : ℕ} (pair : Fin n → Fin n → ℕ → ℕ → ℕ)
    (turn : ℕ) (box : DiscreteBox n) (cycle : List (Fin n × Fin n)) :
    List (DifferenceEdge n) :=
  cycle.map (fun e => ⟨e.1, e.2, boxEdgeWeight pair turn box e.1 e.2⟩)

/-- Actual two-sided lower bounds on every ordered pair. The wrapped
bound uses the outward rounded full turn, so its direction is explicit. -/
def DiscreteAngularBounds {n : ℕ} (pair : Fin n → Fin n → ℕ → ℕ → ℕ)
    (turn : ℕ) (w : Fin n → ℕ) (angle : Fin n → ℝ) : Prop :=
  ∀ i j, i < j → (pair i j (w i) (w j) : ℝ) ≤ angle j - angle i ∧
    (pair i j (w i) (w j) : ℝ) ≤ (turn : ℝ) - (angle j - angle i)

theorem boxEdgeWeight_bound {n : ℕ} (pair : Fin n → Fin n → ℕ → ℕ → ℕ)
    (turn : ℕ) (box : DiscreteBox n) (w : Fin n → ℕ) (angle : Fin n → ℝ)
    (hw : box.Contains w) (ha : DiscreteAngularBounds pair turn w angle) (i j : Fin n) :
    (boxEdgeWeight pair turn box i j : ℝ) ≤ angle j - angle i := by
  by_cases hij : i < j
  · have hm : (boxPairLower pair box i j : ℝ) ≤ pair i j (w i) (w j) := by
      exact_mod_cast boxPairLower_le pair box w hw i j
    simpa [boxEdgeWeight, hij] using hm.trans (ha i j hij).1
  · by_cases hji : j < i
    · have hm : (boxPairLower pair box j i : ℝ) ≤ pair j i (w j) (w i) := by
        exact_mod_cast boxPairLower_le pair box w hw j i
      simp only [boxEdgeWeight, if_neg hij, if_pos hji, Int.cast_sub, Int.cast_natCast]
      linarith [(ha j i hji).2]
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp [boxEdgeWeight]

inductive DiscreteCover (n : ℕ) where
  | budget
  | cycle (start : Fin n) (edges : List (Fin n × Fin n))
  | split (i : Fin n) (cut : ℕ) (left right : DiscreteCover n)

def discreteCoverCheck {n : ℕ} (extra : Fin n → ℕ → ℕ)
    (pair : Fin n → Fin n → ℕ → ℕ → ℕ) (slack turn : ℕ) :
    DiscreteBox n → DiscreteCover n → Bool
  | box, .budget => decide (slack < boxExtraLower extra box)
  | box, .cycle start edges => positiveCycleCheck (boxCycleEdges pair turn box edges) start
  | box, .split i cut left right =>
      discreteCoverCheck extra pair slack turn (box.left i cut).cached left &&
        discreteCoverCheck extra pair slack turn (box.right i cut).cached right

/-- Opaque composition avoids reducing a complete large tree in one
conversion check. Every child proof remains independently kernel checked. -/
theorem discreteCoverCheck_split_true {n : ℕ} (extra : Fin n → ℕ → ℕ)
    (pair : Fin n → Fin n → ℕ → ℕ → ℕ) (slack turn : ℕ)
    (box : DiscreteBox n) (i : Fin n) (cut : ℕ) (left right : DiscreteCover n)
    (hl : discreteCoverCheck extra pair slack turn (box.left i cut).cached left = true)
    (hr : discreteCoverCheck extra pair slack turn (box.right i cut).cached right = true) :
    discreteCoverCheck extra pair slack turn box (.split i cut left right) = true := by
  simp only [discreteCoverCheck, Bool.and_eq_true]
  exact ⟨hl, hr⟩

/-- Coverage, table minima, every cycle edge, and its positive weight are
all kernel checked. Neither a saved word count nor a generator success
flag occurs among the premises. -/
theorem discreteCoverCheck_sound {n : ℕ} (extra : Fin n → ℕ → ℕ)
    (pair : Fin n → Fin n → ℕ → ℕ → ℕ) (slack turn : ℕ)
    (box : DiscreteBox n) (cover : DiscreteCover n)
    (hc : discreteCoverCheck extra pair slack turn box cover = true)
    (w : Fin n → ℕ) (hw : box.Contains w) (angle : Fin n → ℝ)
    (hbudget : (∑ i, extra i (w i)) ≤ slack)
    (hangle : DiscreteAngularBounds pair turn w angle) : False := by
  induction cover generalizing box with
  | budget =>
      have he : slack < boxExtraLower extra box := by simpa [discreteCoverCheck] using hc
      have hm := boxExtraLower_le extra box w hw
      omega
  | cycle start edges =>
      have hcheck : positiveCycleCheck (boxCycleEdges pair turn box edges) start = true := hc
      apply positive_cycle_impossible (boxCycleEdges pair turn box edges)
        (boxCycleEdges pair turn box edges) start angle 1 (by norm_num) hcheck
        (fun _ h => h)
      intro e he
      obtain ⟨ij, _, rfl⟩ := List.mem_map.mp he
      simpa using boxEdgeWeight_bound pair turn box w angle hw hangle ij.1 ij.2
  | split i cut left right ihl ihr =>
      have hs : discreteCoverCheck extra pair slack turn (box.left i cut) left = true ∧
          discreteCoverCheck extra pair slack turn (box.right i cut) right = true := by
        simpa only [discreteCoverCheck, DiscreteBox.cached_eq, Bool.and_eq_true] using hc
      rcases discrete_split_covers box i cut w hw with hl | hr
      · exact ihl _ hs.1 hl
      · exact ihr _ hs.2 hr

end CP15.Certificate
