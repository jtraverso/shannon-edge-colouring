/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ShannonColouring.Shannon
public import ShannonColouring.Sharp

/-!
# Sanity checks for Shannon's theorem

Small cases: `Δ = 0, 1, 2, 3`, a single edge and a triangle, and the sizes of small Shannon
triangles.
-/

@[expose] public section

namespace ShannonColouring

/-! ### The arithmetic of `⌊3Δ/2⌋` -/

theorem shannon_bound_zero : 3 * 0 / 2 = 0 := rfl
theorem shannon_bound_one : 3 * 1 / 2 = 1 := rfl
theorem shannon_bound_two : 3 * 2 / 2 = 3 := rfl
theorem shannon_bound_three : 3 * 3 / 2 = 4 := rfl

/-! ### `Δ = 0`: no edges -/

/-- A multigraph of maximum degree `0` has no edges (Shannon's theorem gives a colouring with
`0` colours). -/
theorem isEmpty_of_degree_le_zero {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (ends : ι → V × V) (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (hΔ : ∀ v, degree ends v ≤ 0) :
    IsEmpty ι := by
  obtain ⟨c, -⟩ := shannon ends hloop 0 hΔ
  exact ⟨fun i => (c i).elim0⟩

/-! ### `Δ = 1`: a matching, one colour -/

/-- A multigraph of maximum degree `1` (a matching) can be properly coloured with one colour. -/
theorem colouring_of_degree_le_one {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (ends : ι → V × V) (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (hΔ : ∀ v, degree ends v ≤ 1) :
    ∃ c : ι → Fin 1, IsProperEdgeColouring ends c :=
  shannon ends hloop 1 hΔ

/-- A single edge. -/
def singleEdge : Unit → Fin 2 × Fin 2 := fun _ => (0, 1)

theorem singleEdge_degree_le (v : Fin 2) : degree singleEdge v ≤ 1 := by
  fin_cases v <;> decide

theorem singleEdge_colourable : ∃ c : Unit → Fin 1, IsProperEdgeColouring singleEdge c :=
  shannon singleEdge (fun _ => by simp [singleEdge]) 1 singleEdge_degree_le

theorem singleEdge_not_colourable_zero :
    ¬ ∃ c : Unit → Fin 0, IsProperEdgeColouring singleEdge c :=
  fun ⟨c, _⟩ => (c ()).elim0

/-! ### `Δ = 2`: the triangle needs three colours -/

/-- The triangle `K₃` with edges `01`, `12`, `02`. -/
def triangle : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (1, 2), (0, 2)]

theorem triangle_loopless (i : Fin 3) : (triangle i).1 ≠ (triangle i).2 := by
  fin_cases i <;> decide

theorem triangle_degree_le (v : Fin 3) : degree triangle v ≤ 2 := by
  fin_cases v <;> decide

/-- Shannon's theorem colours the triangle with `⌊3·2/2⌋ = 3` colours. -/
theorem triangle_colourable : ∃ c : Fin 3 → Fin 3, IsProperEdgeColouring triangle c :=
  shannon triangle triangle_loopless 2 triangle_degree_le

/-- The triangle has no proper edge colouring with `2` colours. -/
theorem triangle_not_colourable_two : ¬ ∃ c : Fin 3 → Fin 2, IsProperEdgeColouring triangle c := by
  rintro ⟨c, hc⟩
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    refine hc i j hne ?_ hij
    fin_cases i <;> fin_cases j <;> simp only [Incident, triangle] <;> decide
  simpa using Fintype.card_le_of_injective c hinj

/-! ### Small Shannon triangles -/

/-- For `Δ = 1` the Shannon triangle is a single edge. -/
theorem card_shannonTriangleEdge_one : Fintype.card (ShannonTriangleEdge 1) = 1 := rfl

/-- For `Δ = 2` the Shannon triangle is the triangle `K₃`. -/
theorem card_shannonTriangleEdge_two : Fintype.card (ShannonTriangleEdge 2) = 3 := rfl

/-- For `Δ = 3` the Shannon triangle has multiplicities `1, 1, 2` and `4 = ⌊9/2⌋` edges. -/
theorem card_shannonTriangleEdge_three : Fintype.card (ShannonTriangleEdge 3) = 4 := rfl

theorem shannonTriangle_three_not_colourable :
    ¬ ∃ c : ShannonTriangleEdge 3 → Fin 3, IsProperEdgeColouring (shannonTriangle 3) c :=
  shannonTriangle_not_colourable 3 3 (by norm_num)

end ShannonColouring
