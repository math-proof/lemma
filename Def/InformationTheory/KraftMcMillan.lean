/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/KraftMcMillan.lean -/

module

public import Mathlib.InformationTheory.Coding.KraftMcMillan
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Def.InformationTheory.PrefixFree
public import Theorem.Real.PrefixFree

@[expose] public section

open scoped BigOperators


namespace MathlibExt.InformationTheory.KraftMcMillan

/-- All words of length `n` over `β`, as a finset. -/
def words (β : Type*) [Fintype β] [DecidableEq β] : ℕ → Finset (List β)
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion fun b => (words β n).image fun tl => b :: tl

end MathlibExt.InformationTheory.KraftMcMillan
