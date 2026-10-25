import Mathlib
import sympy.Basic
import Lemma.ModularCurve.LaurentCoeff
open ModularCurve


/--
[ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent.lean)
-/
@[path]
private lemma main
  [Field κ] [Field k] [Algebra κ k]
  {n : ℕ}
  {f : Fin n → LaurentSeries κ}
-- given
  (hf : LinearIndependent κ f) :
-- imply
  LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by
-- proof
  classical
    set g : κ →+* k := algebraMap κ k with hg
    rw [Fintype.linearIndependent_iff] at hf ⊢
    intro c hc i₀
    let B := Module.Basis.ofVectorSpace κ k
    have hcomb : ∀ j, ∑ i, (B.repr (c i) j) • f i = 0 := by
      intro j
      ext m
      have hm : ∑ i, ((f i).coeff m) • c i = 0 := by
        have h0 := congrArg (fun x : LaurentSeries k => x.coeff m) hc
        simp only [HahnSeries.coeff_zero, HahnSeries.coeff_sum, Function.comp_apply, HahnSeries.coeff_smul, coeffMap_coeff,
          smul_eq_mul] at h0
        rw [← h0]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, mul_comm]
      have hj := congrArg (fun x : k => B.repr x j) hm
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hj
      rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
      simp only [HahnSeries.coeff_smul, smul_eq_mul]
      rw [← hj]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hzero : ∀ j, B.repr (c i₀) j = 0 := fun j => hf _ (hcomb j) i₀
    have hrepr : B.repr (c i₀) = 0 := Finsupp.ext hzero
    simpa using congrArg B.repr.symm hrepr


-- created on 2026-10-23
