import Mathlib
import Lemma.Fin.MulMulMul4SquareCardRothLowIndices.le.CardRothBox.of.Gt_0.Gt_0.All_Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_low_equation_twice_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m d : ℕ}
  {r : Fin m → ℕ}
  {γ : ℝ}
-- given
  (hr : ∀ h, 0 < r h)
  (hm : 0 < m)
  (hγ : 0 < γ)
  (hparam : (d : ℝ) ≤ 2 * m * γ ^ 2) :
-- imply
  2 * Fintype.card (RothLowIndex r γ × Fin d) ≤ Fintype.card (RothBox r) := by
-- proof
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  have hbound :=
    MulMulMul4SquareCardRothLowIndices.le.CardRothBox.of.Gt_0.Gt_0.All_Gt_0 hr hm hγ
  have hreal :
    ((2 * ((rothLowIndices r γ).card * d) : ℕ) : ℝ) ≤
      Fintype.card (RothBox r) := by
    push_cast
    calc
      _ = ((2 : ℝ) * d) * (rothLowIndices r γ).card := by ring
      _ ≤ (4 * m * γ ^ 2) * (rothLowIndices r γ).card := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      _ ≤ Fintype.card (RothBox r) := hbound
  exact_mod_cast hreal


-- created on 2026-10-21
