import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  (P : MvPolynomial (Fin m) R) (i j : RothMvIndex m) :
-- imply
  rothMvHasse j (rothMvHasse i P) =
    (∏ h, (Nat.choose ((i + j) h) (i h) : R)) • rothMvHasse (i + j) P := by
-- proof
  have roth_choose_comp (l i j : ℕ) :
    (l + j).choose j * (l + j + i).choose i =
      (i + j).choose i * (l + (i + j)).choose (i + j) := by
    have h := Nat.choose_mul (n := l + j + i) (k := i + j) (s := i)
      (Nat.le_add_right i j)
    have hsub : l + j + i - i = l + j := by omega
    rw [hsub] at h
    have hk : i + j - i = j := by omega
    rw [hk] at h
    have htotal : l + j + i = l + (i + j) := by omega
    rw [htotal] at h
    rw [htotal]
    simpa only [mul_comm] using h.symm
  ext l
  rw [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
    CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex]
  rw [MvPolynomial.coeff_smul, CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex]
  rw [smul_eq_mul]
  have hprod :
    (∏ h, (Nat.choose ((l + j) h) (j h) : R)) *
      (∏ h, (Nat.choose ((l + j + i) h) (i h) : R)) =
      (∏ h, (Nat.choose ((i + j) h) (i h) : R)) *
        (∏ h, (Nat.choose ((l + (i + j)) h) ((i + j) h) : R)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro h _
    simp only [Finsupp.add_apply]
    rw [← Nat.cast_mul, ← Nat.cast_mul, roth_choose_comp]
  have hindex : l + j + i = l + (i + j) := by
    ext h
    simp only [Finsupp.add_apply]
    omega
  rw [hindex] at hprod
  rw [hindex, ← mul_assoc, ← mul_assoc, hprod]


-- created on 2026-10-21
