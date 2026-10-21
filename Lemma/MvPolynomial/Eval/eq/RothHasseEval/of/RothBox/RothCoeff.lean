import Mathlib
import Lemma.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


/--
[rothMvHasse_eval_ofCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing S]
  {r : Fin m → ℕ} (c : RothCoeff r) (i : RothBox r) (x : Fin m → S) :
-- imply
  MvPolynomial.eval₂ (algebraMap ℤ S) x
    (rothMvHasse (rothBoxIndex i) (rothMvOfCoeff c)) =
    rothHasseEval c (fun h ↦ i h) x := by
-- proof
  classical
  rw [rothMvOfCoeff, rothMvHasse_finset_sum_h Finset.univ]
  rw [MvPolynomial.eval₂_sum]
  unfold rothHasseEval
  apply Finset.sum_congr rfl
  intro j _
  rw [rothMvHasse_monomial_h, MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype]
  ·
    change
      (algebraMap ℤ S) ((∏ h, (Nat.choose (j h) (i h) : ℤ)) * c j) *
        ∏ h, x h ^ ((j h : ℕ) - (i h : ℕ)) = _
    rw [map_mul, map_prod]
    rw [algebraMap_int_eq, Int.coe_castRingHom]
    dsimp only
    simp only [Int.cast_natCast]
    change
      (∏ h, (Nat.choose (j h) (i h) : S)) * (c j : S) *
        ∏ h, x h ^ ((j h : ℕ) - (i h : ℕ)) = _
    rw [Finset.prod_mul_distrib]
    ac_rfl
  ·
    intro h
    simp


-- created on 2026-10-21
