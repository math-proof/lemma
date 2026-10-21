import Mathlib
import Lemma.Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvVanishesBelow_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  {P Q : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
-- given
  (hP : rothMvVanishesBelow P x r a)
  (hQ : rothMvVanishesBelow Q x r b) :
-- imply
  rothMvVanishesBelow (P * Q) x r (a + b) := by
-- proof
  classical
  intro i hi
  rw [map_mul, ← MvPolynomial.notMem_support_iff]
  intro himem
  have hadd := MvPolynomial.support_mul
    (rothTranslate m x P) (rothTranslate m x Q) himem
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hadd
  have hPu : (rothTranslate m x P).coeff u ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hu
  have hQv : (rothTranslate m x Q).coeff v ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hv
  have hwu : a ≤ rothMvWeight r u := by
    by_contra hnot
    exact hPu (hP u (lt_of_not_ge hnot))
  have hwv : b ≤ rothMvWeight r v := by
    by_contra hnot
    exact hQv (hQ v (lt_of_not_ge hnot))
  rw [← huv, RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex] at hi
  linarith


-- created on 2026-10-21
