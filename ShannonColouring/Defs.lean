/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Edge colourings of multigraphs: definitions

A finite loopless multigraph on `V` is an edge family `ends : ι → V × V` with distinct endpoints
(parallel edges allowed). A proper edge colouring gives edges sharing an endpoint different colours.
-/

@[expose] public section

namespace ShannonColouring

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]

/-- Edge `i` is incident with vertex `v`. -/
def Incident (ends : ι → V × V) (i : ι) (v : V) : Prop := (ends i).1 = v ∨ (ends i).2 = v

/-- The degree of `v`: the number of edges incident with `v`. -/
def degree (ends : ι → V × V) (v : V) : ℕ :=
  (Finset.univ.filter fun i => (ends i).1 = v ∨ (ends i).2 = v).card

/-- `c` is a proper edge colouring: distinct edges sharing an endpoint get different colours. -/
def IsProperEdgeColouring (ends : ι → V × V) {k : ℕ} (c : ι → Fin k) : Prop :=
  ∀ i j, i ≠ j → (∃ v, Incident ends i v ∧ Incident ends j v) → c i ≠ c j

end ShannonColouring
