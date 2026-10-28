# Mathlib definitions used in Challenge.lean (Shannon's theorem)

The statements in `Challenge.lean` define their own multigraph notions (`Incident`, `degree`,
`IsProperEdgeColouring`; Mathlib has no multigraphs) and otherwise use only basic notions: `Fin`,
products, `Finset.univ`, `Finset.filter`, `Finset.card` and `Fintype`. Verbatim excerpts at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4; Apache-2.0):

## Finset.filter

`Mathlib/Data/Finset/Filter.lean`, lines 46–53:

```lean
variable (p : α → Prop) [DecidablePred p] {s t : Finset α}

/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩
```

## Finset.card

`Mathlib/Data/Finset/Card.lean`, lines 47–48:

```lean
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## Fintype.card

`Mathlib/Data/Fintype/Card.lean`, line 40:

```lean
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
```
