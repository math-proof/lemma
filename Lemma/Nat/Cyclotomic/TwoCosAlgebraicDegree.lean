import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Cyclotomic.TwoCosAlgebraicDegree
open Polynomial IntermediateField
open MetaMathlibExt


/--
[finrank_adjoin_two_cos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/TwoCosAlgebraicDegree.lean)
-/
@[path]
private lemma finrank_adjoin_two_cos_eq
  {n k : ℕ}
-- given
  (hn : 2 < n)
  (hk : Nat.Coprime k n) :
-- imply
  Module.finrank ℚ ↥(Algebra.adjoin ℚ
    ({2 * Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ))} : Set ℝ)) =
    Nat.totient n / 2 := by
-- proof
  apply MetaMathlibExt.finrank_adjoin_two_cos n k hn hk


-- created on 2026-10-20
