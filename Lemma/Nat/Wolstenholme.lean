import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Wolstenholme
open scoped BigOperators
open MathlibExt.NumberTheory.Wolstenholme


/--
[wolstenholme](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Wolstenholme.lean)
-/
@[path]
private lemma wolstenholme_eq
  {p : ℕ}
-- given
  (hp : p.Prime)
  (h0 : 5 ≤ p) :
-- imply
  ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 2))⁻¹) = 0 := by
-- proof
  apply MathlibExt.NumberTheory.Wolstenholme.wolstenholme p hp h0


-- created on 2026-10-20
