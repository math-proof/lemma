import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.SphericalBuilding.AdaptedBasisProof
open GLnBuilding


/--
[intermediate_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisProof.lean)
-/
@[path]
private lemma intermediate_submodule_eq
  [Field k]
  [AddCommGroup M]
  [Module k M]
  [FiniteDimensional k M]
  {V W : Submodule k M}
-- given
  (hVW : V < W)
  (hgap : finrank k V + 2 ≤ finrank k W) :
-- imply
  ∃ U : Submodule k M, V < U ∧ U < W ∧ finrank k U = finrank k V + 1 := by
-- proof
  apply GLnBuilding.intermediate_submodule hVW hgap

/--
[insertIdx_eq_take_drop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisProof.lean)
-/
@[path]
private lemma insertIdx_eq_take_drop_eq
  [Field k]
  {l : List α}
  {i : ℕ}
  {a : α}
-- given
  (hi : i ≤ l.length) :
-- imply
  l.insertIdx i a = l.take i ++ a :: l.drop i := by
-- proof
  apply GLnBuilding.insertIdx_eq_take_drop l i a hi

/--
[pairwise_insertIdx](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisProof.lean)
-/
@[path]
private lemma pairwise_insertIdx_eq
  [Field k]
  {R : α → α → Prop}
  {l : List α}
  {a : α}
  {i : ℕ}
-- given
  (hi : i ≤ l.length)
  (hpw : l.Pairwise R)
  (hleft : ∀ x ∈ l.take i, R x a)
  (hright : ∀ x ∈ l.drop i, R a x) :
-- imply
  (l.insertIdx i a).Pairwise R := by
-- proof
  apply GLnBuilding.pairwise_insertIdx hi hpw hleft hright

/--
[le_getLast_of_mem_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisProof.lean)
-/
@[path]
private lemma le_getLast_of_mem_pairwise_eq
  [Field k]
  [Preorder α]
  {l : List α}
  {a : α}
-- given
  (hpw : l.Pairwise (· < ·))
  (hne : l ≠ [])
  (ha : a ∈ l) :
-- imply
  a ≤ l.getLast hne := by
-- proof
  apply GLnBuilding.le_getLast_of_mem_pairwise hpw hne ha

/--
[head_le_of_mem_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisProof.lean)
-/
@[path]
private lemma head_le_of_mem_pairwise_eq
  [Field k]
  [Preorder α]
  {l : List α}
  {a : α}
-- given
  (hpw : l.Pairwise (· < ·))
  (hne : l ≠ [])
  (ha : a ∈ l) :
-- imply
  l.head hne ≤ a := by
-- proof
  apply GLnBuilding.head_le_of_mem_pairwise hpw hne ha

/--
[extend_flag_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisProof.lean)
-/
@[path]
private lemma extend_flag_chain_eq
  [Field k]
  {n : ℕ}
  {chain : List (Submodule k (Vec k n))}
-- given
  (hne : chain ≠ [])
  (hchain : chain.IsChain (· < ·))
  (hproper : ∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤)
  (hshort : chain.length < n - 1) :
-- imply
  ∃ (chain' : List (Submodule k (Vec k n))), chain'.length = chain.length + 1 ∧ chain'.IsChain (· < ·) ∧ (∀ V ∈ chain', V ≠ ⊥ ∧ V ≠ ⊤) ∧ chain'.length ≤ n - 1 ∧ (∀ V ∈ chain, V ∈ chain') := by
-- proof
  apply GLnBuilding.extend_flag_chain n chain hne hchain hproper hshort

/--
[flag_completion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisProof.lean)
-/
@[path]
private lemma flag_completion_eq
  [Field k]
  {n : ℕ}
  {chain : List (Submodule k (Vec k n))}
-- given
  (hn : n ≥ 2)
  (hne : chain ≠ [])
  (hchain : chain.IsChain (· < ·))
  (hproper : ∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤) :
-- imply
  ∃ (chain' : List (Submodule k (Vec k n))), chain'.length = n - 1 ∧ chain'.IsChain (· < ·) ∧ (∀ V ∈ chain', V ≠ ⊥ ∧ V ≠ ⊤) ∧ (∀ V ∈ chain, V ∈ chain') := by
-- proof
  apply GLnBuilding.flag_completion n hn chain hne hchain hproper


-- created on 2026-10-23
