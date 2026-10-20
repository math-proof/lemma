import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Matching.BergeLemma
open scoped symmDiff


/--
[berge_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/BergeLemma.lean)
-/
@[path]
private lemma berge_general_eq
  [Finite V]
  {G : SimpleGraph V}
  {M : G.Subgraph}
-- given
  (hM : M.IsMatching) :
-- imply
  (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ↔
    ¬ ∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
    p.support.Nodup ∧ u ∉ M.verts ∧ v ∉ M.verts ∧
    List.IsChain (fun e₁ e₂ => (e₁ ∈ M.edgeSet) ≠ (e₂ ∈ M.edgeSet)) p.edges ∧
    0 < p.length := by
-- proof
  apply berge_general G M hM

/--
[Berge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/BergeLemma.lean)
-/
@[path]
private lemma Berge_eq
  :
-- imply
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    (M : Finset (Sym2 V)),
    (∀ e ∈ M, e ∈ G.edgeSet) →
    (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) →
    ((∀ (M' : Finset (Sym2 V)),
    (∀ e ∈ M', e ∈ G.edgeSet) →
    (∀ e₁ ∈ M', ∀ e₂ ∈ M', e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) →
    M'.card ≤ M.card) ↔
    ¬ ∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
    p.support.Nodup ∧ (∀ e ∈ M, u ∉ e) ∧ (∀ e ∈ M, v ∉ e) ∧
    List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges ∧ 0 < p.length) := by
-- proof
  apply Berge


-- created on 2026-10-20
