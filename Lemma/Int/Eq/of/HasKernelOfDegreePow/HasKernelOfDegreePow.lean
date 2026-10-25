import Mathlib
import sympy.Basic
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Lemma.Int.P2MUtil

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

/--
[CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow.lean)
-/
@[path]
private lemma main
  [CommRing B] [Nontrivial B]
  {p : ℕ} [Fact p.Prime]
  {φ : Series B}
  {h h' : ℕ}
-- given
  (hh : FormalODModule.HasKernelOfDegree φ (p ^ h))
  (hh' : FormalODModule.HasKernelOfDegree φ (p ^ h')) :
-- imply
  h = h' := by
-- proof
  classical
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have e1 := hh.2.2 (B ⧸ 𝔪) (Ideal.Quotient.mk 𝔪)
  have e2 := hh'.2.2 (B ⧸ 𝔪) (Ideal.Quotient.mk 𝔪)
  have hp : p ^ h = p ^ h' := e1.symm.trans e2
  refine Nat.pow_right_injective (Fact.out : p.Prime).two_le hp


-- created on 2026-10-23
