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

open Classical in
/-- The generalized Turán number unfolds to the exact filtered `Finset.sup`
expression: the supremum of `G.copyCount T` over all `H`-free hosts on
`Fin n`. -/
theorem generalizedExtremalNumber_eq_sup (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β) :
    generalizedExtremalNumber n T H =
      Finset.sup (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
        (fun G => G.copyCount T) := by
  classical
  unfold generalizedExtremalNumber
  rfl

/-- Every `H`-free host graph `G` on `Fin n` has at most the generalized Turán
number of copies of `T`: `G.copyCount T ≤ generalizedExtremalNumber n T H`. -/
theorem copyCount_le_generalizedExtremalNumber (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β)
    (G : SimpleGraph (Fin n)) (hG : H.Free G) :
    G.copyCount T ≤ generalizedExtremalNumber n T H := by
  classical
  unfold generalizedExtremalNumber
  apply Finset.le_sup (s := Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
    (f := fun G => G.copyCount T) (b := G)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩

/-- Upper-bound characterization: the generalized Turán number is at most `m`
if and only if every `H`-free host has at most `m` copies of `T`. -/
theorem generalizedExtremalNumber_le_iff (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β)
    (m : ℕ) :
    generalizedExtremalNumber n T H ≤ m ↔
      ∀ G : SimpleGraph (Fin n), H.Free G → G.copyCount T ≤ m := by
  classical
  unfold generalizedExtremalNumber
  rw [Finset.sup_le_iff]
  constructor
  · intro h G hG
    exact h _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩)
  · intro h b hb
    exact h b (Finset.mem_filter.mp hb).2

/-- Attainment: when at least one `H`-free host graph on `Fin n` exists, some
`H`-free host attains the generalized Turán number. -/
theorem exists_free_copyCount_eq_generalizedExtremalNumber (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β)
    (hne : ∃ G : SimpleGraph (Fin n), H.Free G) :
    ∃ G : SimpleGraph (Fin n), H.Free G ∧ G.copyCount T = generalizedExtremalNumber n T H := by
  classical
  have hne' : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G)).Nonempty := by
    obtain ⟨G0, hG0⟩ := hne
    exact ⟨G0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG0⟩⟩
  have hEx : ∃ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G),
      Finset.sup
        (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
        (fun G => G.copyCount T) = G.copyCount T :=
    Finset.exists_mem_eq_sup
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G)) hne'
      (fun G => G.copyCount T)
  obtain ⟨G, hGmem, hEq⟩ := hEx
  have hFree : H.Free G := (Finset.mem_filter.mp hGmem).2
  have hdef := generalizedExtremalNumber_eq_sup n T H
  exact ⟨G, hFree, hEq.symm.trans hdef.symm⟩

end SimpleGraph
