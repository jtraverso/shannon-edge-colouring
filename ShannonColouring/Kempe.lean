/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ShannonColouring.Defs
public import ShannonColouring.PathEnds

/-!
# Partial edge colourings and Kempe changes

We work with colourings that are proper on a finite set `s` of edges, missing colours at
vertices, and Kempe changes: swapping two colours `α`, `γ` on all `α`/`γ`-coloured edges of a
union of components of the `α`/`γ`-subgraph.
-/

@[expose] public section

namespace ShannonColouring

variable {V ι : Type*}

/-- `c` is proper on the edge set `s`. -/
def ProperOn (ends : ι → V × V) (s : Finset ι) {k : ℕ} (c : ι → Fin k) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (∃ v, Incident ends i v ∧ Incident ends j v) → c i ≠ c j

/-- The colour `δ` is missing at `x`: no edge of `s` at `x` has colour `δ`. -/
def Misses (ends : ι → V × V) (s : Finset ι) {k : ℕ} (c : ι → Fin k) (x : V) (δ : Fin k) :
    Prop :=
  ∀ i ∈ s, Incident ends i x → c i ≠ δ

variable {ends : ι → V × V} {k : ℕ}

theorem ProperOn.mono {s t : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) (hts : t ⊆ s) :
    ProperOn ends t c := fun i hi j hj => h i (hts hi) j (hts hj)

theorem Misses.mono {s t : Finset ι} {c : ι → Fin k} {x : V} {δ : Fin k}
    (h : Misses ends s c x δ) (hts : t ⊆ s) : Misses ends t c x δ := fun i hi => h i (hts hi)

/-- Colouring a new edge with a colour missing at both of its ends. -/
theorem ProperOn.extend [DecidableEq ι] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {e : ι}
    (he : e ∉ s) {δ : Fin k} (h1 : Misses ends s c (ends e).1 δ)
    (h2 : Misses ends s c (ends e).2 δ) : ProperOn ends (insert e s) (Function.update c e δ) := by
  have hm : ∀ j ∈ s, (∃ v, Incident ends e v ∧ Incident ends j v) → c j ≠ δ := by
    rintro j hj ⟨v, hev, hjv⟩
    rcases hev with rfl | rfl
    · exact h1 j hj hjv
    · exact h2 j hj hjv
  intro i hi j hj hij hv
  rw [Finset.mem_insert] at hi hj
  rcases hi with rfl | hi <;> rcases hj with rfl | hj
  · exact absurd rfl hij
  · have hje : j ≠ i := fun h => he (h ▸ hj)
    simp only [Function.update_self, Function.update_of_ne hje]
    exact (hm j hj hv).symm
  · have hie : i ≠ j := fun h => he (h ▸ hi)
    simp only [Function.update_self, Function.update_of_ne hie]
    obtain ⟨v, h1, h2⟩ := hv
    exact hm i hi ⟨v, h2, h1⟩
  · have hie : i ≠ e := fun h => he (h ▸ hi)
    have hje : j ≠ e := fun h => he (h ▸ hj)
    simp only [Function.update_of_ne hie, Function.update_of_ne hje]
    exact h i hi j hj hij hv

/-- Recolouring an edge with a colour missing at both of its ends. -/
theorem ProperOn.recolour [DecidableEq ι] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {f : ι}
    (hf : f ∈ s) {δ : Fin k} (hδ : ∀ x, Incident ends f x → Misses ends s c x δ) :
    ProperOn ends s (Function.update c f δ) := by
  have := (h.mono (Finset.erase_subset f s)).extend (Finset.notMem_erase f s)
    ((hδ _ (Or.inl rfl)).mono (Finset.erase_subset f s))
    ((hδ _ (Or.inr rfl)).mono (Finset.erase_subset f s))
  rwa [Finset.insert_erase hf] at this

/-- Colours on a vertex: in a proper colouring, distinct edges at `x` have distinct colours. -/
theorem ProperOn.ne_of_incident {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) {x : V} (hix : Incident ends i x)
    (hjx : Incident ends j x) : c i ≠ c j := h i hi j hj hij ⟨x, hix, hjx⟩

/-- Recolour an edge `f` at `u` from `β` to `α` (missing at both ends of `f`), and then colour the
new edge `e = uv` with `β`, assuming `β` is missing at `v`. -/
theorem ProperOn.recolour_extend [DecidableEq ι] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {e f : ι}
    (he : e ∉ s) (hf : f ∈ s) {α β : Fin k} (hfu : Incident ends f (ends e).1) (hcf : c f = β)
    (hα : ∀ x, Incident ends f x → Misses ends s c x α) (hβ : Misses ends s c (ends e).2 β) :
    ∃ c' : ι → Fin k, ProperOn ends (insert e s) c' := by
  have h1 := h.recolour hf hα
  refine ⟨_, h1.extend he (δ := β) ?_ ?_⟩
  · intro i hi hiu
    by_cases hif : i = f
    · subst hif
      rw [Function.update_self]
      intro hαβ
      exact hα _ hfu i hi hfu (hcf.trans hαβ.symm)
    · rw [Function.update_of_ne hif, ← hcf]
      exact h.ne_of_incident hi hf hif hiu hfu
  · intro i hi hiv
    by_cases hif : i = f
    · subst hif
      exact absurd hcf (hβ i hi hiv)
    · rw [Function.update_of_ne hif]
      exact hβ i hi hiv

/-! ### The Kempe graph and Kempe changes -/

/-- The simple graph of the `α`/`γ`-coloured edges of `s` (parallel edges merged). -/
def kempeGraph (ends : ι → V × V) (s : Finset ι) (c : ι → Fin k) (α γ : Fin k) :
    SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ i ∈ s, (c i = α ∨ c i = γ) ∧
    ((ends i).1 = a ∧ (ends i).2 = b ∨ (ends i).1 = b ∧ (ends i).2 = a)
  symm := ⟨by
    rintro a b ⟨hab, i, hi, hc, h⟩
    exact ⟨hab.symm, i, hi, hc, h.symm⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

theorem kempeGraph_adj_ends (hloop : ∀ i, (ends i).1 ≠ (ends i).2) {s : Finset ι}
    {c : ι → Fin k} {α γ : Fin k} {i : ι} (hi : i ∈ s) (hc : c i = α ∨ c i = γ) :
    (kempeGraph ends s c α γ).Adj (ends i).1 (ends i).2 :=
  ⟨hloop i, i, hi, hc, Or.inl ⟨rfl, rfl⟩⟩

/-- The degree of a vertex in the Kempe graph is bounded by the number of available colours
among `α`, `γ` at that vertex. -/
theorem kempeGraph_degree_le [Fintype V] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c)
    {α γ : Fin k} [DecidableRel (kempeGraph ends s c α γ).Adj] (x : V) (D : Finset (Fin k))
    (hD : ∀ i ∈ s, Incident ends i x → (c i = α ∨ c i = γ) → c i ∈ D) :
    (kempeGraph ends s c α γ).degree x ≤ D.card := by
  classical
  let E := s.filter fun i => Incident ends i x ∧ (c i = α ∨ c i = γ)
  let other : ι → V := fun i => if (ends i).1 = x then (ends i).2 else (ends i).1
  have hsub : (kempeGraph ends s c α γ).neighborFinset x ⊆ E.image other := by
    intro b hb
    rw [SimpleGraph.mem_neighborFinset] at hb
    obtain ⟨hxb, i, hi, hc, hends⟩ := hb
    rw [Finset.mem_image]
    refine ⟨i, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨hi, ?_, hc⟩
      simp only [Incident]
      rcases hends with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
    · simp only [other]
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2]
      · simp [h1, Ne.symm hxb]
  have hinj : Set.InjOn c E := by
    intro i hi j hj hij
    simp only [E, Finset.coe_filter, Set.mem_setOf_eq] at hi hj
    by_contra hne
    exact h.ne_of_incident hi.1 hj.1 hne hi.2.1 hj.2.1 hij
  have himg : E.image c ⊆ D := by
    intro d hd
    simp only [E, Finset.mem_image, Finset.mem_filter] at hd
    obtain ⟨i, ⟨hi, hix, hc⟩, rfl⟩ := hd
    exact hD i hi hix hc
  calc (kempeGraph ends s c α γ).degree x
      = ((kempeGraph ends s c α γ).neighborFinset x).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ (E.image other).card := Finset.card_le_card hsub
    _ ≤ E.card := Finset.card_image_le
    _ = (E.image c).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ D.card := Finset.card_le_card himg

open Classical in
/-- The Kempe change: swap `α` and `γ` on the `α`/`γ`-coloured edges with first end in `T`. -/
noncomputable def kempeSwap (ends : ι → V × V) (c : ι → Fin k) (α γ : Fin k) (T : Set V) :
    ι → Fin k :=
  fun i => if (ends i).1 ∈ T ∧ (c i = α ∨ c i = γ) then Equiv.swap α γ (c i) else c i

/-- `T` is a union of components of the `α`/`γ`-subgraph of `s`. -/
def KempeClosed (ends : ι → V × V) (s : Finset ι) (c : ι → Fin k) (α γ : Fin k) (T : Set V) :
    Prop :=
  ∀ i ∈ s, (c i = α ∨ c i = γ) → ((ends i).1 ∈ T ↔ (ends i).2 ∈ T)

theorem KempeClosed.mem_of_incident {s : Finset ι} {c : ι → Fin k} {α γ : Fin k} {T : Set V}
    (hT : KempeClosed ends s c α γ T) {i : ι} (hi : i ∈ s) (hc : c i = α ∨ c i = γ) {x : V}
    (hx : Incident ends i x) : x ∈ T ↔ (ends i).1 ∈ T := by
  rcases hx with rfl | rfl
  · exact Iff.rfl
  · exact (hT i hi hc).symm

theorem kempeSwap_of_not {c : ι → Fin k} {α γ : Fin k} {T : Set V} {i : ι}
    (hc : ¬ (c i = α ∨ c i = γ)) : kempeSwap ends c α γ T i = c i := by
  simp [kempeSwap, hc]

open Classical in
theorem kempeSwap_mem_or {c : ι → Fin k} {α γ : Fin k} {T : Set V} {i : ι}
    (hc : c i = α ∨ c i = γ) :
    kempeSwap ends c α γ T i = (if (ends i).1 ∈ T then Equiv.swap α γ (c i) else c i) := by
  simp [kempeSwap, hc]

theorem swap_mem_or {α γ d : Fin k} (hd : d = α ∨ d = γ) :
    Equiv.swap α γ d = α ∨ Equiv.swap α γ d = γ := by
  rcases hd with rfl | rfl
  · right; exact Equiv.swap_apply_left _ _
  · left; exact Equiv.swap_apply_right _ _

/-- A Kempe change preserves properness. -/
theorem ProperOn.kempeSwap {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {α γ : Fin k}
    {T : Set V} (hT : KempeClosed ends s c α γ T) :
    ProperOn ends s (kempeSwap ends c α γ T) := by
  intro i hi j hj hij ⟨x, hix, hjx⟩
  have hne := h.ne_of_incident hi hj hij hix hjx
  by_cases hci : c i = α ∨ c i = γ <;> by_cases hcj : c j = α ∨ c j = γ
  · rw [kempeSwap_mem_or hci, kempeSwap_mem_or hcj]
    have ei := hT.mem_of_incident hi hci hix
    have ej := hT.mem_of_incident hj hcj hjx
    by_cases hxT : x ∈ T
    · rw [if_pos (ei.mp hxT), if_pos (ej.mp hxT)]
      exact fun heq => hne ((Equiv.swap α γ).injective heq)
    · rw [if_neg (fun h' => hxT (ei.mpr h')), if_neg (fun h' => hxT (ej.mpr h'))]
      exact hne
  · rw [kempeSwap_of_not hcj, kempeSwap_mem_or hci]
    split_ifs
    · intro heq; exact hcj (heq ▸ swap_mem_or hci)
    · exact hne
  · rw [kempeSwap_of_not hci, kempeSwap_mem_or hcj]
    split_ifs
    · intro heq; exact hci (heq ▸ swap_mem_or hcj)
    · exact hne
  · rw [kempeSwap_of_not hci, kempeSwap_of_not hcj]
    exact hne

/-- Outside `T`, missing colours are unchanged by a Kempe change. -/
theorem Misses.kempeSwap_of_notMem {s : Finset ι} {c : ι → Fin k} {α γ : Fin k} {T : Set V}
    (hT : KempeClosed ends s c α γ T) {x : V} (hx : x ∉ T) {δ : Fin k}
    (h : Misses ends s c x δ) : Misses ends s (kempeSwap ends c α γ T) x δ := by
  intro i hi hix
  by_cases hci : c i = α ∨ c i = γ
  · rw [kempeSwap_mem_or hci, if_neg (fun h' => hx ((hT.mem_of_incident hi hci hix).mpr h'))]
    exact h i hi hix
  · rw [kempeSwap_of_not hci]
    exact h i hi hix

/-- Inside `T`, a Kempe change swaps the missing colours `α` and `γ`. -/
theorem Misses.kempeSwap_of_mem {s : Finset ι} {c : ι → Fin k} {α γ : Fin k} {T : Set V}
    (hT : KempeClosed ends s c α γ T) {x : V} (hx : x ∈ T) {δ : Fin k}
    (h : Misses ends s c x (Equiv.swap α γ δ)) : Misses ends s (kempeSwap ends c α γ T) x δ := by
  intro i hi hix
  by_cases hci : c i = α ∨ c i = γ
  · rw [kempeSwap_mem_or hci, if_pos ((hT.mem_of_incident hi hci hix).mp hx)]
    intro heq
    apply h i hi hix
    rw [← heq, Equiv.swap_apply_self]
  · rw [kempeSwap_of_not hci]
    intro heq
    apply h i hi hix
    rw [heq, Equiv.swap_apply_of_ne_of_ne]
    · intro h'; exact hci (Or.inl (heq.trans h'))
    · intro h'; exact hci (Or.inr (heq.trans h'))

/-- The vertex set of the component of `z` in the Kempe graph is Kempe-closed. -/
theorem kempeClosed_reachable (hloop : ∀ i, (ends i).1 ≠ (ends i).2) {s : Finset ι}
    {c : ι → Fin k} {α γ : Fin k} (z : V) :
    KempeClosed ends s c α γ {x | (kempeGraph ends s c α γ).Reachable z x} := by
  intro i hi hc
  have hadj := kempeGraph_adj_ends hloop hi hc
  exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.reachable.symm⟩

end ShannonColouring
