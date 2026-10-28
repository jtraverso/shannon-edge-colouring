/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Components of graphs of maximum degree two

In a finite simple graph of maximum degree at most `2`, a connected component contains at most
two vertices of degree at most `1`. This is the combinatorial fact behind Kempe-chain arguments:
a two-coloured subgraph of a properly edge-coloured graph has maximum degree `2`, so each of its
components is a path or a cycle, and a path has only two ends.
-/

@[expose] public section

namespace ShannonColouring

open SimpleGraph

/-- In a finite simple graph of maximum degree at most `2`, three distinct vertices of degree at
most `1` can not lie in a common connected component. -/
theorem not_three_ends_in_component {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hdeg : ∀ x, H.degree x ≤ 2) {u v w : V} (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) (hv : H.Reachable u v) (hw : H.Reachable u w) (du : H.degree u ≤ 1)
    (dv : H.degree v ≤ 1) (dw : H.degree w ≤ 1) : False := by
  classical
  set C := H.connectedComponentMk u
  set s : Set V := C.supp
  have hcon : (H.induce s).Connected := C.connected_toSimpleGraph
  have hus : u ∈ s := rfl
  have hvs : v ∈ s := (ConnectedComponent.eq.mpr hv).symm
  have hws : w ∈ s := (ConnectedComponent.eq.mpr hw).symm
  have hnb : ∀ x : s, H.neighborSet x ⊆ s := by
    intro x y hy
    have hx : (x : V) ∈ s := x.2
    change H.connectedComponentMk y = C
    rw [← hx]
    exact (ConnectedComponent.eq.mpr (Adj.reachable hy)).symm
  have hdegeq : ∀ x : s, (H.induce s).degree x = H.degree x := fun x =>
    degree_induce_of_neighborSet_subset (hnb x)
  have h1 := hcon.card_vert_le_card_edgeSet_add_one
  have h2 := sum_degrees_eq_twice_card_edges (H.induce s)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at h1
  simp only [hdegeq] at h2
  set u' : s := ⟨u, hus⟩
  set v' : s := ⟨v, hvs⟩
  set w' : s := ⟨w, hws⟩
  have hsum : ∑ x : s, H.degree x + 3 ≤ 2 * Fintype.card s := by
    have hu1 : u' ∈ (Finset.univ : Finset s) := Finset.mem_univ _
    have hv1 : v' ∈ (Finset.univ.erase u' : Finset s) := by
      simp [u', v', Subtype.ext_iff, Ne.symm huv]
    have hw1 : w' ∈ ((Finset.univ.erase u').erase v' : Finset s) := by
      simp [u', v', w', Subtype.ext_iff, Ne.symm huw, Ne.symm hvw]
    rw [← Finset.add_sum_erase _ _ hu1, ← Finset.add_sum_erase _ _ hv1,
      ← Finset.add_sum_erase _ _ hw1]
    have hrest : ∑ x ∈ ((Finset.univ.erase u').erase v').erase w', H.degree x ≤
        2 * (((Finset.univ.erase u').erase v').erase w').card := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun x _ => hdeg x
    have hc : (((Finset.univ.erase u').erase v').erase w').card + 3 = Fintype.card s := by
      rw [Finset.card_erase_of_mem hw1, Finset.card_erase_of_mem hv1,
        Finset.card_erase_of_mem hu1, Finset.card_univ]
      have : 3 ≤ Fintype.card s := by
        have := Finset.card_le_univ ({u', v', w'} : Finset s)
        rw [Finset.card_insert_of_notMem (by simp [u', v', w', Subtype.ext_iff, huv, huw]),
          Finset.card_insert_of_notMem (by simp [v', w', Subtype.ext_iff, hvw]),
          Finset.card_singleton] at this
        omega
      omega
    have du' : H.degree (u' : V) ≤ 1 := du
    have dv' : H.degree (v' : V) ≤ 1 := dv
    have dw' : H.degree (w' : V) ≤ 1 := dw
    omega
  omega

end ShannonColouring
