module
public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part5
public import Theorem.Fin.MulMulMul4SquareCardRothLowIndices.le.CardRothBox.of.Gt_0.Gt_0.All_Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


public section

private abbrev RothLowIndex {m : ℕ} (r : Fin m → ℕ) (γ : ℝ) :=
  {i : RothBox r // i ∈ rothLowIndices r γ}

/--
[roth_low_equation_twice_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
