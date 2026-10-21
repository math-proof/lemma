import Mathlib
import Lemma.Fin.CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex
import Lemma.Fin.EqRothLastIndexCastSucc.of.RothMvIndex
import Lemma.Fin.RothMvL1.eq.Sum_NatAbsCoeff
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_lastEquiv_coeff_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (P : MvPolynomial (Fin (n + 1)) ℤ)
  (a : ℕ) :
-- imply
  rothMvL1 ((rothLastEquiv ℤ n P).coeff a) ≤ rothMvL1 P := by
-- proof
  classical
  let Q := (rothLastEquiv ℤ n P).coeff a
  let f : RothMvIndex n → RothMvIndex (n + 1) := fun i ↦ rothLastIndex i a
  have hf : Function.Injective f := by
    intro i j hij
    ext h
    have := congrArg (fun d : RothMvIndex (n + 1) ↦ d h.castSucc) hij
    simpa [f, EqRothLastIndexCastSucc.of.RothMvIndex] using this
  have hsubset : Q.support.image f ⊆ P.support := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    apply MvPolynomial.mem_support_iff.mpr
    rw [← CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex]
    exact MvPolynomial.mem_support_iff.mp hi
  rw [RothMvL1.eq.Sum_NatAbsCoeff, RothMvL1.eq.Sum_NatAbsCoeff]
  calc
    _ = ∑ d ∈ Q.support.image f, (P.coeff d).natAbs := by
      rw [Finset.sum_image]
      ·
        apply Finset.sum_congr rfl
        intro i _
        rw [CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex]
      ·
        exact fun _ _ _ _ hij ↦ hf hij
    _ ≤ ∑ d ∈ P.support, (P.coeff d).natAbs :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦ Nat.zero_le _)


-- created on 2026-10-21
