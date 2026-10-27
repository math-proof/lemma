import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.TakagiFunction
open MetaMathlibExt


/--
[TakagiFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/TakagiFunction.lean)
-/
@[path]
private lemma takagi_bit_eq_eq
-- given
  (n : Nat)
  (i : Int) :
-- imply
  takagiBit n i =
    (if 0 ≤ i then (if Nat.testBit n i.toNat then 1 else 0) else 0) := by
-- proof
  apply MetaMathlibExt.takagiBit_eq n i

/--
[TakagiFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/TakagiFunction.lean)
-/
@[path]
private lemma takagi_ell_zero_eq
-- given
  (n : Nat)
  (k : Int) :
-- imply
  takagiEll n k 0 = 0 := by
-- proof
  apply MetaMathlibExt.takagiEll_zero n k

/--
[TakagiFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/TakagiFunction.lean)
-/
@[path]
private lemma takagi_ell_succ_eq
-- given
  (n : Nat)
  (k : Int)
  (i : Nat) :
-- imply
  takagiEll n k (i + 1) =
    (if takagiBit n (k - (i : Int)) = 0 then
      ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))
    else i - ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))) := by
-- proof
  apply MetaMathlibExt.takagiEll_succ n k i

/--
[TakagiFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/TakagiFunction.lean)
-/
@[path]
private lemma takagi_newdef_eq_eq
-- given
  (n : Nat)
  (k : Int) :
-- imply
  takagiNewdef n k =
    ∑' i, (takagiEll n k (i + 1) : Real) / 2 ^ (i + 1) := by
-- proof
  apply MetaMathlibExt.takagiNewdef_eq n k

/--
[TakagiFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/TakagiFunction.lean)
-/
@[path]
private lemma takagi_bit_neg_eq
-- given
  (n : Nat)
  (i : Int)
  (h : i < 0) :
-- imply
  takagiBit n i = 0 := by
-- proof
  apply MetaMathlibExt.takagiBit_neg n i h

/--
[TakagiFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/TakagiFunction.lean)
-/
@[path]
private lemma takagi_ell_one_eq
-- given
  (n : Nat)
  (k : Int) :
-- imply
  takagiEll n k 1 = 0 := by
-- proof
  apply MetaMathlibExt.takagiEll_one n k


-- created on 2026-10-11
