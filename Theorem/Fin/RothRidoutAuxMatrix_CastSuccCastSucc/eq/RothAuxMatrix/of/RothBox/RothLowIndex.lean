module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.NumberTheory.RothAuxiliary.Part3
public import Def.NumberTheory.RothAuxiliary.Part7
open MathlibExt.NumberTheory.RothAuxiliary


public section

/--
[rothRidoutAuxMatrix_old_row](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
-- given
  (i : RothLowIndex r γ)
  (k : Fin (rothIntegralPolynomial α).natDegree)
  (j : RothBox r) :
-- imply
  rothRidoutAuxMatrix α r γ (i, k.castSucc.castSucc) j =
    rothAuxMatrix α r γ (i, k) j := by
-- proof
  simp [rothRidoutAuxMatrix]


-- updated on 2026-11-13
-- created on 2026-10-21
