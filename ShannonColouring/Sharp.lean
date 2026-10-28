/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ShannonColouring.Defs

/-!
# Sharpness of Shannon's bound: the Shannon triangle

The Shannon triangle `shannonTriangle Δ` has vertices `0, 1, 2` with `⌊Δ/2⌋` parallel edges
`01`, `⌊Δ/2⌋` parallel edges `02` and `⌈Δ/2⌉ = ⌊(Δ+1)/2⌋` parallel edges `12`.

* The degrees are `2⌊Δ/2⌋ ≤ Δ`, `⌊Δ/2⌋ + ⌈Δ/2⌉ = Δ` and `Δ`.
* Any two edges share a vertex, so a proper edge colouring uses a different colour on every edge.
* The number of edges is `2⌊Δ/2⌋ + ⌈Δ/2⌉ = ⌊3Δ/2⌋`: for `Δ = 2t` it is `3t`, and for
  `Δ = 2t + 1` it is `2t + (t + 1) = 3t + 1 = ⌊(6t + 3)/2⌋`.

So the multiplicities `⌊Δ/2⌋, ⌊Δ/2⌋, ⌈Δ/2⌉` give exactly `⌊3Δ/2⌋` edges also for odd `Δ`,
and no adjustment is needed.
-/

@[expose] public section

namespace ShannonColouring

/-- Edges of the Shannon triangle: `⌊Δ/2⌋` edges `01`, `⌊Δ/2⌋` edges `02`, `⌈Δ/2⌉` edges `12`. -/
abbrev ShannonTriangleEdge (Δ : ℕ) : Type := Fin (Δ / 2) ⊕ Fin (Δ / 2) ⊕ Fin ((Δ + 1) / 2)

/-- The ends of the edges of the Shannon triangle. -/
def shannonTriangle (Δ : ℕ) : ShannonTriangleEdge Δ → Fin 3 × Fin 3
  | .inl _ => (0, 1)
  | .inr (.inl _) => (0, 2)
  | .inr (.inr _) => (1, 2)

theorem shannonTriangle_loopless (Δ : ℕ) (i : ShannonTriangleEdge Δ) :
    (shannonTriangle Δ i).1 ≠ (shannonTriangle Δ i).2 := by
  rcases i with _ | _ | _ <;> simp [shannonTriangle]

theorem degree_shannonTriangle_le (Δ : ℕ) (v : Fin 3) : degree (shannonTriangle Δ) v ≤ Δ := by
  rw [degree, Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' Δ <;>
  fin_cases v <;> simp [shannonTriangle] <;> omega

/-- Any two edges of the Shannon triangle share an end. -/
theorem shannonTriangle_adjacent (Δ : ℕ) (i j : ShannonTriangleEdge Δ) :
    ∃ v, Incident (shannonTriangle Δ) i v ∧ Incident (shannonTriangle Δ) j v := by
  rcases i with _ | _ | _ <;> rcases j with _ | _ | _ <;>
  simp only [Incident, shannonTriangle] <;> decide

theorem card_shannonTriangleEdge (Δ : ℕ) : Fintype.card (ShannonTriangleEdge Δ) = 3 * Δ / 2 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' Δ <;> omega

/-- A proper edge colouring of the Shannon triangle needs at least `⌊3Δ/2⌋` colours. -/
theorem shannonTriangle_not_colourable (Δ k : ℕ) (hk : k < 3 * Δ / 2) :
    ¬ ∃ c : ShannonTriangleEdge Δ → Fin k, IsProperEdgeColouring (shannonTriangle Δ) c := by
  rintro ⟨c, hc⟩
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    exact hc i j hne (shannonTriangle_adjacent Δ i j) hij
  have := Fintype.card_le_of_injective c hinj
  rw [card_shannonTriangleEdge, Fintype.card_fin] at this
  omega

/-- **Sharpness of Shannon's theorem**: for every `Δ` the Shannon triangle is a loopless
multigraph of maximum degree at most `Δ` with no proper edge colouring with fewer than
`⌊3Δ/2⌋` colours. -/
theorem shannon_sharp (Δ : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (ends : ι → Fin 3 × Fin 3),
    (∀ i, (ends i).1 ≠ (ends i).2) ∧ (∀ v, degree ends v ≤ Δ) ∧
    ∀ k < 3 * Δ / 2, ¬ ∃ c : ι → Fin k, IsProperEdgeColouring ends c :=
  ⟨ShannonTriangleEdge Δ, inferInstance, shannonTriangle Δ, shannonTriangle_loopless Δ,
    degree_shannonTriangle_le Δ, shannonTriangle_not_colourable Δ⟩

end ShannonColouring
