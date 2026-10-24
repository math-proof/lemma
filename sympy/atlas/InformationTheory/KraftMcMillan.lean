/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/KraftMcMillan.lean -/

import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.atlas.InformationTheory.PrefixFree
import Lemma.Real.PrefixFree
open scoped BigOperators

namespace MathlibExt.InformationTheory.KraftMcMillan

/-- All words of length `n` over `β`, as a finset. -/
private def words (β : Type*) [Fintype β] [DecidableEq β] : ℕ → Finset (List β)
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion fun b => (words β n).image fun tl => b :: tl
end MathlibExt.InformationTheory.KraftMcMillan
