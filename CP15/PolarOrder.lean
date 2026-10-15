import CP15.OuterRingOrder

namespace CP15

/-- Sort distinct polar directions without changing the point set.
The returned index map is a permutation, so no point or contact is lost.
This theorem is used only after proving polar-argument injectivity. -/
theorem exists_sorted_polar_permutation {n : ℕ} (q : Fin n → Plane)
    (hinj : Function.Injective (fun i => polarArg (q i))) :
    ∃ src : Fin n → Fin n, ∃ φ : Fin n → ℝ,
      Function.Bijective src ∧ StrictMono φ ∧
      (∀ i, polarArg (q (src i)) = φ i) ∧
      (∀ i, -Real.pi < φ i ∧ φ i ≤ Real.pi) := by
  classical
  let angles : Finset ℝ := Finset.univ.image (fun i => polarArg (q i))
  have hcard : angles.card = n := by
    dsimp [angles]
    simpa using Finset.card_image_of_injective Finset.univ hinj
  let order := angles.orderEmbOfFin rfl
  let ix (i : Fin n) : Fin angles.card := ⟨i.val, by rw [hcard]; exact i.isLt⟩
  let φ : Fin n → ℝ := fun i => order (ix i)
  have hmono : StrictMono φ := by
    intro i j hij
    exact order.strictMono (show ix i < ix j by simpa [ix] using hij)
  have hmem (i : Fin n) : φ i ∈ angles :=
    Finset.orderEmbOfFin_mem angles rfl (ix i)
  let src (i : Fin n) : Fin n :=
    Classical.choose (Finset.mem_image.mp (hmem i))
  have harg (i : Fin n) : polarArg (q (src i)) = φ i :=
    (Classical.choose_spec (Finset.mem_image.mp (hmem i))).2
  have hsrc : Function.Injective src := by
    intro i j h
    apply hmono.injective
    calc
      φ i = polarArg (q (src i)) := (harg i).symm
      _ = polarArg (q (src j)) := by rw [h]
      _ = φ j := harg j
  refine ⟨src, φ, ⟨hsrc, Finite.surjective_of_injective hsrc⟩,
    hmono, harg, ?_⟩
  intro i
  rw [← harg i]
  exact polarArg_range (q (src i))

end CP15
