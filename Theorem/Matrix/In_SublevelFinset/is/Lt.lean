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
private theorem mem_sublevel_finset_iff
-- given
  (S : NonnegativeDiscreteSpectrum)
  (Λ : ℝ)
  (j : ℕ) :
-- imply
  j ∈ S.sublevelFinset Λ ↔ S j < Λ := by
-- proof
  apply NonnegativeDiscreteSpectrum.mem_sublevelFinset S Λ j

-- created on 2026-10-10
-- updated on 2026-10-26
