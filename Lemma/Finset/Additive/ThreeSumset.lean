import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Additive.ThreeSumset
open scoped Pointwise
open MetaMathlibExt


/--
[gyarmatiMatolcsiRuzsa_three_sumset_zmod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean)
-/
@[path]
private lemma gyarmatiMatolcsiRuzsa_three_sumset_zmod_eq
  {p : ℕ}
  {A B C : Finset (ZMod p)}
-- given
  (hp : Nat.Prime p)
  (hodd : Odd p) :
-- imply
  ((A + B + C).card : ℕ) ^ 2 ≤ (A + B).card * (B + C).card * (C + A).card := by
-- proof
  apply MetaMathlibExt.gyarmatiMatolcsiRuzsa_three_sumset_zmod p hp hodd A B C


-- created on 2026-10-20
