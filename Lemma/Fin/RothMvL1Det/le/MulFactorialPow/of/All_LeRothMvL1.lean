import Mathlib
import Lemma.Fin.RothMvL1_Sum.le.Sum_RothMvL1
import Lemma.Fin.RothMvL1_Prod.le.Prod_RothMvL1
import Lemma.Fin.RothMvL1Neg.eq.RothMvL1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_det_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k B : ℕ}
  (M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℤ))
-- given
  (hM : ∀ s t, rothMvL1 (M s t) ≤ B) :
-- imply
  rothMvL1 M.det ≤ k.factorial * B ^ k := by
-- proof
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ ∈ Finset.univ, rothMvL1 (Equiv.Perm.sign σ • ∏ i, M (σ i) i) :=
      RothMvL1_Sum.le.Sum_RothMvL1 Finset.univ _
    _ = ∑ σ : Equiv.Perm (Fin k), rothMvL1 (∏ i, M (σ i) i) := by
      apply Finset.sum_congr rfl
      intro σ _
      obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
      · simp [hsign]
      · simp [hsign, RothMvL1Neg.eq.RothMvL1]
    _ ≤ ∑ _ : Equiv.Perm (Fin k), B ^ k := by
      gcongr with σ
      apply le_trans (RothMvL1_Prod.le.Prod_RothMvL1 Finset.univ _)
      apply le_trans _ (le_of_eq (by simp : (∏ _ : Fin k, B) = B ^ k))
      gcongr with i
      exact hM (σ i) i
    _ = k.factorial * B ^ k := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      rfl


-- created on 2026-10-21
