/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ShannonColouring.Kempe

/-!
# Shannon's theorem on edge colourings of multigraphs

C. E. Shannon, *A theorem on coloring the lines of a network*, J. Math. Phys. 28 (1949) 148–152:
every loopless multigraph of maximum degree at most `Δ` has a proper edge colouring with
`⌊3Δ/2⌋` colours.

## Proof

Induction on the set of coloured edges. Let `k = ⌊3Δ/2⌋`, so `3Δ ≤ 2k + 1` and `Δ ≤ k`. Let
`e = uv` be a new edge and `c` a proper colouring of the old edges. Write `M(x)` for the set of
colours missing at `x`; then `|M(u)|, |M(v)| ≥ k - Δ + 1` and `|M(x)| ≥ k - Δ` for all `x`.

1. If `M(u) ∩ M(v) ≠ ∅`, colour `e` with a common missing colour.
2. Otherwise pick `β ∈ M(v)`; the `β`-edge `f` at `u` goes to some `w ∉ {u, v}`. If some
   `α ∈ M(u) ∩ M(w)`, recolour `f` with `α` and colour `e` with `β`.
3. Otherwise `M(u)` is disjoint from `M(v)` and from `M(w)`, and
   `|M(u)| + |M(v)| + |M(w)| ≥ 3k - 3Δ + 2 > k`, so there is `γ ∈ M(v) ∩ M(w)`. Pick `α ∈ M(u)`.
   In the `α`/`γ`-subgraph the vertices `u`, `v`, `w` have degree at most one, so they are not all
   in the same component (a component is a path or a cycle). If `u` is not in the component of
   `v`, swap `α`, `γ` there and colour `e` with `α`. Otherwise `w` is not in the component of `v`
   (which contains `u`); swap `α`, `γ` in the component of `w` (this does not touch `u`, `v` or
   the colour `β` of `f`), and then proceed as in step 2.
-/

@[expose] public section

namespace ShannonColouring

open Classical

variable {V ι : Type*} [DecidableEq V] [Fintype ι]

/-- The number of edges of `s` at `x` is at most the degree of `x`. -/
theorem card_incident_le (ends : ι → V × V) (s : Finset ι) (x : V) :
    (s.filter fun i => Incident ends i x).card ≤ degree ends x := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi; simp only [Incident] at hi
  simp [hi.2]

/-- If the edge `e ∉ s` is at `x`, then `s` has fewer edges at `x` than the degree of `x`. -/
theorem card_incident_lt (ends : ι → V × V) {s : Finset ι} {e : ι} (he : e ∉ s) {x : V}
    (hex : Incident ends e x) :
    (s.filter fun i => Incident ends i x).card + 1 ≤ degree ends x := by
  have hsub : insert e (s.filter fun i => Incident ends i x) ⊆
      Finset.univ.filter fun i => (ends i).1 = x ∨ (ends i).2 = x := by
    intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · simpa [Incident] using hex
    · rw [Finset.mem_filter] at hi; simp only [Incident] at hi
      simp [hi.2]
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (fun h => he (Finset.mem_filter.mp h).1)] at this
  exact this

omit [DecidableEq V] [Fintype ι] in
/-- Counting missing colours: at least `k` minus the number of edges at `x`. -/
theorem card_misses_add {k : ℕ} (ends : ι → V × V) (s : Finset ι) (c : ι → Fin k) (x : V) :
    k ≤ (Finset.univ.filter (Misses ends s c x)).card +
      (s.filter fun i => Incident ends i x).card := by
  have hsub : (Finset.univ : Finset (Fin k)) ⊆
      Finset.univ.filter (Misses ends s c x) ∪ (s.filter fun i => Incident ends i x).image c := by
    intro δ _
    by_cases hδ : Misses ends s c x δ
    · exact Finset.mem_union_left _ (by simpa using hδ)
    · apply Finset.mem_union_right
      simp only [Misses, not_forall, not_not] at hδ
      obtain ⟨i, hi, hix, rfl⟩ := hδ
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hi, hix⟩)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  refine h1.trans ((Finset.card_union_le _ _).trans ?_)
  convert Nat.add_le_add_left Finset.card_image_le _ using 2

/-- A vertex `x` misses at least `k - Δ` colours. -/
theorem card_misses_ge {k Δ : ℕ} {ends : ι → V × V} (hΔ : ∀ v, degree ends v ≤ Δ)
    (s : Finset ι) (c : ι → Fin k) (x : V) :
    k ≤ (Finset.univ.filter (Misses ends s c x)).card + Δ := by
  have h1 := card_misses_add ends s c x
  have h2 := card_incident_le ends s x
  have h3 := hΔ x
  omega

/-- An end `x` of the new edge `e ∉ s` misses at least `k - Δ + 1` colours. -/
theorem card_misses_ge_of_incident {k Δ : ℕ} {ends : ι → V × V} (hΔ : ∀ v, degree ends v ≤ Δ)
    {s : Finset ι} {e : ι} (he : e ∉ s) (c : ι → Fin k) {x : V} (hex : Incident ends e x) :
    k + 1 ≤ (Finset.univ.filter (Misses ends s c x)).card + Δ := by
  have h1 := card_misses_add ends s c x
  have h2 := card_incident_lt ends he hex
  have h3 := hΔ x
  omega

/-- The induction step of Shannon's theorem: a proper colouring of `s` with `k` colours,
`3Δ ≤ 2k + 1`, can be modified into a proper colouring of `insert e s`. -/
theorem exists_properOn_insert [Fintype V] {k Δ : ℕ} {ends : ι → V × V}
    (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (hΔ : ∀ v, degree ends v ≤ Δ) (hk : 3 * Δ ≤ 2 * k + 1)
    {s : Finset ι} {e : ι} (he : e ∉ s) {c : ι → Fin k} (hc : ProperOn ends s c) :
    ∃ c' : ι → Fin k, ProperOn ends (insert e s) c' := by
  set u := (ends e).1 with hu_def
  set v := (ends e).2 with hv_def
  have huv : u ≠ v := hloop e
  have hAu := card_misses_ge_of_incident hΔ he c (x := u) (Or.inl rfl)
  have hAv := card_misses_ge_of_incident hΔ he c (x := v) (Or.inr rfl)
  -- Step 1: a common missing colour.
  by_cases h1 : ∃ δ, Misses ends s c u δ ∧ Misses ends s c v δ
  · obtain ⟨δ, h1u, h1v⟩ := h1
    exact ⟨_, hc.extend he h1u h1v⟩
  push_neg at h1
  -- choose `β ∈ M(v)` and the `β`-edge `f` at `u`
  obtain ⟨β, hβ⟩ : (Finset.univ.filter (Misses ends s c v)).Nonempty := by
    rw [← Finset.card_pos]
    convert (show 0 < _ by omega : 0 < (Finset.univ.filter (Misses ends s c v)).card)
  have hβv : Misses ends s c v β := by simpa using hβ
  have hβu : ¬ Misses ends s c u β := fun h => h1 β h hβv
  simp only [Misses, not_forall, not_not] at hβu
  obtain ⟨f, hf, hfu, hcf⟩ := hβu
  set w := if (ends f).1 = u then (ends f).2 else (ends f).1 with hw_def
  have hfends : ∀ x, Incident ends f x → x = u ∨ x = w := by
    rintro x (rfl | rfl)
    · by_cases h : (ends f).1 = u
      · exact Or.inl h
      · right; simp [w, h]
    · by_cases h : (ends f).1 = u
      · right; simp [w, h]
      · left
        rcases hfu with h' | h'
        · exact absurd h' h
        · exact h'
  have hfw : Incident ends f w := by
    by_cases h : (ends f).1 = u
    · right; simp [w, h]
    · left; simp [w, h]
  have hwu : w ≠ u := by
    intro h
    by_cases h' : (ends f).1 = u
    · exact hloop f (h'.trans (by simpa [w, h'] using h.symm))
    · simp [w, h'] at h
  have hwv : w ≠ v := by
    intro h
    exact hβv f hf (h ▸ hfw) hcf
  -- Step 2: a colour missing at `u` and `w`.
  by_cases h2 : ∃ α, Misses ends s c u α ∧ Misses ends s c w α
  · obtain ⟨α, h2u, h2w⟩ := h2
    refine hc.recolour_extend he hf hfu hcf (α := α) ?_ hβv
    intro x hx
    rcases hfends x hx with rfl | rfl
    · exact h2u
    · exact h2w
  push_neg at h2
  -- Step 3: counting gives `γ ∈ M(v) ∩ M(w)`.
  have hAw := card_misses_ge hΔ s c w
  obtain ⟨γ, hγv, hγw⟩ : ∃ γ, Misses ends s c v γ ∧ Misses ends s c w γ := by
    by_contra h3
    push_neg at h3
    have d1 : Disjoint (Finset.univ.filter (Misses ends s c u))
        (Finset.univ.filter (Misses ends s c v) ∪ Finset.univ.filter (Misses ends s c w)) := by
      rw [Finset.disjoint_union_right]
      constructor
      · rw [Finset.disjoint_filter]; exact fun δ _ h => h1 δ h
      · rw [Finset.disjoint_filter]; exact fun δ _ h => h2 δ h
    have d2 : Disjoint (Finset.univ.filter (Misses ends s c v))
        (Finset.univ.filter (Misses ends s c w)) := by
      rw [Finset.disjoint_filter]; exact fun δ _ h => h3 δ h
    have hcard := Finset.card_le_univ (Finset.univ.filter (Misses ends s c u) ∪
      (Finset.univ.filter (Misses ends s c v) ∪ Finset.univ.filter (Misses ends s c w)))
    rw [Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2,
      Fintype.card_fin] at hcard
    omega
  -- choose `α ∈ M(u)`
  obtain ⟨α, hα⟩ : (Finset.univ.filter (Misses ends s c u)).Nonempty := by
    rw [← Finset.card_pos]
    convert (show 0 < _ by omega : 0 < (Finset.univ.filter (Misses ends s c u)).card)
  have hαu : Misses ends s c u α := by simpa using hα
  -- the Kempe graph of `α`, `γ`
  set H := kempeGraph ends s c α γ with hH
  have hdeg : ∀ x, H.degree x ≤ 2 := fun x =>
    (kempeGraph_degree_le hc x {α, γ} (fun i _ _ hci => by
      rcases hci with h | h <;> simp [h])).trans Finset.card_le_two
  have hdu : H.degree u ≤ 1 := by
    refine (kempeGraph_degree_le hc u {γ} (fun i hi hiu hci => ?_)).trans
      (Finset.card_singleton _).le
    rcases hci with h | h
    · exact absurd h (hαu i hi hiu)
    · simp [h]
  have hdv : H.degree v ≤ 1 := by
    refine (kempeGraph_degree_le hc v {α} (fun i hi hiv hci => ?_)).trans
      (Finset.card_singleton _).le
    rcases hci with h | h
    · simp [h]
    · exact absurd h (hγv i hi hiv)
  have hdw : H.degree w ≤ 1 := by
    refine (kempeGraph_degree_le hc w {α} (fun i hi hiw hci => ?_)).trans
      (Finset.card_singleton _).le
    rcases hci with h | h
    · simp [h]
    · exact absurd h (hγw i hi hiw)
  by_cases hr1 : H.Reachable v u
  · by_cases hr2 : H.Reachable v w
    · exact (not_three_ends_in_component H hdeg huv.symm hwv.symm hwu.symm hr1 hr2 hdv hdu
        hdw).elim
    · -- Kempe change at the component of `w`, then recolour `f`.
      set T : Set V := {x | H.Reachable w x}
      have hT : KempeClosed ends s c α γ T := kempeClosed_reachable hloop w
      have huT : u ∉ T := fun h => hr2 (hr1.trans h.symm)
      have hvT : v ∉ T := fun h => hr2 h.symm
      have hwT : w ∈ T := SimpleGraph.Reachable.refl w
      have hc' := hc.kempeSwap hT
      have hβα : β ≠ α := fun h => hαu f hf hfu (hcf.trans h)
      have hβγ : β ≠ γ := fun h => hγw f hf hfw (hcf.trans h)
      have hcf' : kempeSwap ends c α γ T f = β := by
        rw [kempeSwap_of_not (by rw [hcf]; tauto)]; exact hcf
      refine hc'.recolour_extend he hf hfu hcf' (α := α) ?_ (hβv.kempeSwap_of_notMem hT hvT)
      intro x hx
      rcases hfends x hx with rfl | rfl
      · exact hαu.kempeSwap_of_notMem hT huT
      · exact Misses.kempeSwap_of_mem hT hwT (by rw [Equiv.swap_apply_left]; exact hγw)
  · -- Kempe change at the component of `v`, then colour `e` with `α`.
    set T : Set V := {x | H.Reachable v x}
    have hT : KempeClosed ends s c α γ T := kempeClosed_reachable hloop v
    have hvT : v ∈ T := SimpleGraph.Reachable.refl v
    have hc' := hc.kempeSwap hT
    exact ⟨_, hc'.extend he (hαu.kempeSwap_of_notMem hT hr1)
      (Misses.kempeSwap_of_mem hT hvT (by rw [Equiv.swap_apply_left]; exact hγv))⟩

/-- Every subset of the edges can be properly coloured with `⌊3Δ/2⌋` colours. -/
theorem exists_properOn [Fintype V] {ends : ι → V × V} (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (Δ : ℕ)
    (hΔ : ∀ v, degree ends v ≤ Δ) (s : Finset ι) :
    ∃ c : ι → Fin (3 * Δ / 2), ProperOn ends s c := by
  induction s using Finset.induction_on with
  | empty =>
    by_cases hι : IsEmpty ι
    · exact ⟨isEmptyElim, fun i => isEmptyElim i⟩
    · obtain ⟨i⟩ := not_isEmpty_iff.mp hι
      have h1 := card_incident_lt ends (Finset.notMem_empty i) (x := (ends i).1) (Or.inl rfl)
      have h2 := hΔ (ends i).1
      exact ⟨fun _ => ⟨0, by omega⟩, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert e s he ih =>
    obtain ⟨c, hc⟩ := ih
    exact exists_properOn_insert hloop hΔ (by omega) he hc

/-- **Shannon's theorem** (1949): a loopless multigraph of maximum degree at most `Δ` has a
proper edge colouring with `⌊3Δ/2⌋` colours. -/
theorem shannon {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] (ends : ι → V × V)
    (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (Δ : ℕ) (hΔ : ∀ v, degree ends v ≤ Δ) :
    ∃ c : ι → Fin (3 * Δ / 2), IsProperEdgeColouring ends c := by
  obtain ⟨c, hc⟩ := exists_properOn hloop Δ hΔ Finset.univ
  exact ⟨c, fun i j hij hv => hc i (Finset.mem_univ i) j (Finset.mem_univ j) hij hv⟩

end ShannonColouring
