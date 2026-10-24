/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/GeneralizedExtremal.lean -/

import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

/-!
# Generalized Turán number

Source: Alon and Shikhelman, "Many T copies in H-free graphs,"
arXiv:1409.4192v2, TeX lines 85-87:
"For two graphs T and H with no isolated vertices and for an integer n,
let ex(n,T,H) denote the maximum possible number of copies of T in an
H-free graph on n vertices."

This module defines `SimpleGraph.generalizedExtremalNumber` from that source,
using Mathlib's `SimpleGraph.copyCount`, `SimpleGraph.Free`, and the
`Finset.sup` pattern used by `SimpleGraph.extremalNumber`.

The source assumes `T` and `H` have no isolated vertices; this is documented
as the intended domain. The definition and lemmas below are stated more
generally without that hypothesis.
-/

namespace SimpleGraph

/-- Generalized Turán number `ex(n, T, H)`: the maximum possible number of
copies of pattern `T` in an `H`-free host graph on `n` vertices. `G.copyCount T`
counts copies of pattern `T` in host `G`, and `H.Free G` states that `G` is
`H`-free. The intended domain from the source is patterns `T` and `H` with no
isolated vertices; the definition itself does not require this.

The total definition follows Mathlib's `Finset.sup` convention used by
`SimpleGraph.extremalNumber`: it is the supremum of `G.copyCount T` over the
filtered family `Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G)`.
As with `Finset.sup` over `ℕ`, the value is `0` when the filtered family is
empty. -/
noncomputable def generalizedExtremalNumber (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β) : ℕ := by
  classical
  exact Finset.sup (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
    (fun G => G.copyCount T)
end SimpleGraph
