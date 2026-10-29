# Shannon's theorem on edge colourings of multigraphs in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

C. E. Shannon, *A theorem on coloring the lines of a network*, J. Math. Phys. 28 (1949) 148–152,
[doi:10.1002/sapm1949281148](https://doi.org/10.1002/sapm1949281148): **every loopless multigraph
of maximum degree at most `Δ` has a proper edge colouring with `⌊3Δ/2⌋` colours**, and the bound is
attained by the Shannon triangle. Neither result is in Mathlib.

| Lean (namespace `ShannonTheorem`) | Statement |
|---|---|
| `shannon` | A loopless multigraph with all degrees at most `Δ` has a proper edge colouring with `⌊3Δ/2⌋` colours. |
| `shannon_sharp` | For every `Δ`, some loopless multigraph on three vertices with all degrees at most `Δ` has no proper edge colouring with fewer than `⌊3Δ/2⌋` colours. |

A finite multigraph is an edge family `ends : ι → V × V` (parallel edges allowed); `degree` counts
incident edges and a proper edge colouring gives edges sharing an endpoint different colours.

Mathlib does have multigraphs: `Graph α β` in `Mathlib.Combinatorics.Graph.Basic` has a vertex set,
an edge set and an incidence relation `IsLink e x y`, and allows loops and parallel edges. At the
pinned revision it has no degree or edge-colouring notions, so this project does not build on it:
the statements use the edge family above, on finite types with the whole types as vertex and edge
sets. A loopless `G : Graph α β` with finite vertex and edge sets corresponds to such a family
(edges of `G.edgeSet` as indices, each sent to its two ends), but no bridge to `Graph` is proved
here.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the statements; it imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`ShannonColouring/`](ShannonColouring): the proofs.
- [`comparator.json`](comparator.json), [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md),
  [`formalization.yaml`](formalization.yaml).

## How the proof goes

Induction on the set of coloured edges, with `k = ⌊3Δ/2⌋` colours (`ShannonColouring/Shannon.lean`).
For a new edge `uv`, if `u` and `v` miss a common colour, use it. Otherwise take a colour `β`
missing at `v` and the `β`-edge `uw`; if `u` and `w` miss a common colour `α`, recolour `uw` with `α`
and `uv` with `β`. Otherwise a counting argument gives a colour `γ` missing at both `v` and `w`,
and a Kempe change on an `α`/`γ` component (`Kempe.lean`; components of a graph of maximum degree
two have at most two ends, `PathEnds.lean`) reduces to the previous cases. The Shannon triangle
(`Sharp.lean`) has `⌊Δ/2⌋`, `⌊Δ/2⌋` and `⌈Δ/2⌉` parallel edges between its three pairs of
vertices; any two edges meet, so it needs `⌊3Δ/2⌋` colours. Small cases are checked in
`Sanity.lean`.

## Provenance and checks

The theorems were chosen by the author. The proofs were produced by Harmonic's Aristotle (on Lean
4.28) from the formal statements and a proof route, audited, and migrated to Lean `v4.35.0-rc3` and
the module system with Claude (Claude Code). Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`: `lake build`; no `sorry`; `#print axioms` gives only
`propext`, `Classical.choice`, `Quot.sound`; the elaborated statements and definitions of the
Challenge and the Solution are identical (`pp.all`).
