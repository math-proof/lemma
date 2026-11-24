module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part4
open scoped BigOperators


public section

/--
[DiscreteSpectrum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
private theorem ext_eq
-- given
  {S T : NonnegativeDiscreteSpectrum}
  (h : ∀ j, S j = T j) :
-- imply
  S = T := by
-- proof
  apply NonnegativeDiscreteSpectrum.ext h

-- created on 2026-10-10
-- updated on 2026-10-26
