/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import ShannonColouring.Shannon
public import ShannonColouring.Sharp

/-!
# Proofs of the statements in `Challenge.lean`

The definitions are copied verbatim from `Challenge.lean`. The theorems are those of the library
`ShannonColouring` (`ShannonColouring/Shannon.lean`, `ShannonColouring/Sharp.lean`), whose
definitions are literally the same.
-/

@[expose] public section

namespace ShannonTheorem

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]

/-- Edge `i` is incident with vertex `v`. -/
def Incident (ends : ι → V × V) (i : ι) (v : V) : Prop := (ends i).1 = v ∨ (ends i).2 = v

/-- The degree of `v`: the number of edges incident with `v`. -/
def degree (ends : ι → V × V) (v : V) : ℕ :=
  (Finset.univ.filter fun i => (ends i).1 = v ∨ (ends i).2 = v).card

/-- `c` is a proper edge colouring: distinct edges sharing an endpoint get different colours. -/
def IsProperEdgeColouring (ends : ι → V × V) {k : ℕ} (c : ι → Fin k) : Prop :=
  ∀ i j, i ≠ j → (∃ v, Incident ends i v ∧ Incident ends j v) → c i ≠ c j

/-- **Shannon's theorem** (1949): a loopless multigraph of maximum degree at most `Δ` has a
proper edge colouring with `⌊3Δ/2⌋` colours. -/
theorem shannon {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] (ends : ι → V × V)
    (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (Δ : ℕ) (hΔ : ∀ v, degree ends v ≤ Δ) :
    ∃ c : ι → Fin (3 * Δ / 2), IsProperEdgeColouring ends c :=
  ShannonColouring.shannon ends hloop Δ hΔ

/-- **Sharpness of Shannon's theorem**: for every `Δ` there is a loopless multigraph on three
vertices of maximum degree at most `Δ` with no proper edge colouring with fewer than `⌊3Δ/2⌋`
colours. -/
theorem shannon_sharp (Δ : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (ends : ι → Fin 3 × Fin 3),
    (∀ i, (ends i).1 ≠ (ends i).2) ∧ (∀ v, degree ends v ≤ Δ) ∧
    ∀ k < 3 * Δ / 2, ¬ ∃ c : ι → Fin k, IsProperEdgeColouring ends c :=
  ShannonColouring.shannon_sharp Δ

end ShannonTheorem
