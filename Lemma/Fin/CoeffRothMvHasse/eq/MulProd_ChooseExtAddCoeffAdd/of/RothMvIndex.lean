import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvHasse_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  (i k : RothMvIndex m) (P : MvPolynomial (Fin m) R) :
-- imply
  (rothMvHasse i P).coeff k =
    (∏ h, (Nat.choose ((k + i) h) (i h) : R)) * P.coeff (k + i) := by
-- proof
  classical
  unfold rothMvHasse
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single (k + i)]
  ·
    have hki : k + i - i = k := by
      ext h
      simp
    simp only [hki, ite_true]
  ·
    intro j hj hne
    split_ifs with heq
    ·
      if hle : i ≤ j then
        exfalso
        apply hne
        ext h
        have heqh := congrArg (fun x : RothMvIndex m ↦ x h) heq
        have hleh := hle h
        simp only [Finsupp.add_apply]
        apply (tsub_eq_iff_eq_add_of_le hleh).mp heqh
      else
        obtain ⟨h, hh⟩ := not_forall.mp hle
        have hh' : j h < i h := Nat.not_le.mp hh
        have hz : (Nat.choose (j h) (i h) : R) = 0 := by
          simp [Nat.choose_eq_zero_of_lt hh']
        rw [Finset.prod_eq_zero (Finset.mem_univ h) hz, zero_mul]
    ·
      simp
  ·
    intro hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    simp


-- created on 2026-10-21
