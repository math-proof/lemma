import Mathlib
import sympy.Basic
import Lemma.ModularCurve.EichlerShimuraData
import Lemma.ModularCurve.ArithmeticGalois
import Lemma.AlgebraicCurve.Repartitions
import Lemma.Int.P2MUtil

open AlgebraicCurve ModularCurve

/--
[ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ.lean)
-/

def Pic0TorsionEquivSubtype (K F : Type*) [Field K] [Field F] [Algebra K F] (n : ℕ) :
  Pic0.torsion K F n ≃ {x : Pic0 K F // n • x = 0} :=
  Equiv.subtypeEquivRight (fun x => (Pic0.mem_torsion).trans (by rw [natCast_zsmul]))

private lemma  Pic0.natCard_torsion_eq_natCard_subtype (K F : Type*) [Field K] [Field F] [Algebra K F]
  (n : ℕ) : Nat.card (Pic0.torsion K F n) = Nat.card {x : Pic0 K F // n • x = 0} :=
  Nat.card_congr (Pic0TorsionEquivSubtype K F n)
@[path]
private lemma main
  {N : ℕ} [NeZero N]
  {p : ℕ} [Fact p.Prime]
  {k : ℕ}
-- given
  (hK1 : CardinalityAJ p (JZero N) (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) :
-- imply
  Finite (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) := by
-- proof
  apply Nat.finite_of_card_ne_zero
  rw [Pic0.natCard_torsion_eq_natCard_subtype]
  have h := hK1 k
  rw [h]
  exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero


-- created on 2026-10-23
