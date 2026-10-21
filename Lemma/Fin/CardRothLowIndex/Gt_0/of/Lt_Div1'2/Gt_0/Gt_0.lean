import Mathlib
import Lemma.Fin.RothZeroBox.in.RothLowIndices.of.Lt_Div1'2.Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_low_equation_card_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m d : ℕ}
  {r : Fin m → ℕ}
  {γ : ℝ}
-- given
  (hm : 0 < m)
  (hd : 0 < d)
  (hγ : γ < 1 / 2) :
-- imply
  0 < Fintype.card (RothLowIndex r γ × Fin d) := by
-- proof
  apply Fintype.card_pos_iff.mpr
  exact ⟨(⟨rothZeroBox r, RothZeroBox.in.RothLowIndices.of.Lt_Div1'2.Gt_0 hm hγ r⟩, ⟨0, hd⟩)⟩


-- created on 2026-10-21
