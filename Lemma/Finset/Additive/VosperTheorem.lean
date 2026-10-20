import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Additive.VosperTheorem
open scoped Pointwise
open MetaMathlibExt


/--
[vosper_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/VosperTheorem.lean)
-/
@[path]
private lemma vosper_eq_iff_eq
  {p : ℕ} [Fact (Nat.Prime p)]
  {A B : Finset (ZMod p)}
-- given
  (hA : A.Nonempty)
  (hB : B.Nonempty)
  (hAB : A + B ≠ Finset.univ) :
-- imply
  (A + B).card = A.card + B.card - 1 ↔
    (min A.card B.card = 1 ∨
    ((A + B).card = p - 1 ∧
    ∃ c : ZMod p,
    Finset.filter (fun x => x ∉ (A + B)) Finset.univ = {c} ∧
    B = Finset.filter
    (fun x => x ∉ Finset.image (fun a => c - a) A) Finset.univ) ∨
    AreFiniteArithmeticProgressionsWithCommonDifference A B) := by
-- proof
  apply MetaMathlibExt.vosper_eq_iff A B hA hB hAB


-- created on 2026-10-20
