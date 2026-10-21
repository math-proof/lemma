import Mathlib
import Lemma.Fin.MulMulMul4SquareCardRothLowIndices.le.CardRothBox.of.Gt_0.Gt_0.All_Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_low_equation_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
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
  (hparam : (d : ℝ) < 4 * m * γ ^ 2) :
-- imply
  Fintype.card (RothLowIndex r γ × Fin d) < Fintype.card (RothBox r) := by
-- proof
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  if hL : (rothLowIndices r γ).card = 0 then
    simp only [hL, zero_mul]
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun h ↦ ⟨0, Nat.succ_pos (r h)⟩⟩
  else
    have hLpos : (0 : ℝ) < (rothLowIndices r γ).card := by
      exact_mod_cast Nat.pos_of_ne_zero hL
    have hstrict :
      (d : ℝ) * (rothLowIndices r γ).card <
        (4 * m * γ ^ 2) * (rothLowIndices r γ).card :=
      mul_lt_mul_of_pos_right hparam hLpos
    have hbound :=
      MulMulMul4SquareCardRothLowIndices.le.CardRothBox.of.Gt_0.Gt_0.All_Gt_0 hr hm hγ
    have hreal :
      ((d * (rothLowIndices r γ).card : ℕ) : ℝ) <
        Fintype.card (RothBox r) := by
      norm_num only [Nat.cast_mul]
      apply hstrict.trans_le hbound
    have hnat : d * (rothLowIndices r γ).card < Fintype.card (RothBox r) := by
      exact_mod_cast hreal
    simpa [mul_comm] using hnat


-- created on 2026-10-21
