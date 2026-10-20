import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.DobinskiBell
open MetaMathlibExt


/--
[dobinski_formula_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DobinskiBell.lean)
-/
@[path]
private lemma dobinski_formula_hasSum_eq
  {n : Nat} :
-- imply
  HasSum (fun k : Nat => (k : Real) ^ n / (k.factorial : Real))
    (Real.exp 1 * (Nat.bell n : Real)) := by
-- proof
  apply MetaMathlibExt.dobinski_formula_hasSum n


-- created on 2026-10-20
