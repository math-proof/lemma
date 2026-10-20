import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ProthTheorem
open MetaMathlibExt


/--
[proth_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProthTheorem.lean)
-/
@[path]
private lemma proth_theorem_eq
  {h k N : ℕ}
-- given
  (hOdd : Odd h)
  (hlt : h < 2 ^ k)
  (hN : N = h * 2 ^ k + 1) :
-- imply
  Nat.Prime N ↔ ∃ a : ZMod N, a ^ ((N - 1) / 2) = -1 := by
-- proof
  apply MetaMathlibExt.proth_theorem h k N hOdd hlt hN


-- created on 2026-10-20
