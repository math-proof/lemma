/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean -/

/-
Author: @toskua, Avocado
-/


import Theorem.RingTheory.Polynomial.Eisenstein.AdjoinRoot
import Lemma.Int.Polynomial.Eisenstein.AdjoinRoot
import Mathlib.NumberTheory.Padics.PadicIntegers
import Def.MathlibExtTest.RingTheory.Polynomial.Eisenstein.AdjoinRoot
open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (f : A[X]) (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic) (hdeg : 0 < f.natDegree)


namespace ConcretePadicEisenstein

lemma padicEisenstein_monic : padicEisenstein.Monic := by
  exact monic_X_pow_sub_C (2 : PadicA) (by decide)

lemma padicEisenstein_natDegree : padicEisenstein.natDegree = 2 := by
  exact natDegree_X_pow_sub_C

lemma padicEisenstein_natDegree_pos : 0 < padicEisenstein.natDegree := by
  rw [padicEisenstein_natDegree]
  decide

lemma padicEisenstein_isEisenstein :
    padicEisenstein.IsEisensteinAt (IsLocalRing.maximalIdeal PadicA) := by
  refine padicEisenstein_monic.isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal PadicA).ne_top ?_ ?_
  · intro n hn
    rw [padicEisenstein_natDegree] at hn
    interval_cases n <;>
      simp [padicEisenstein, PadicInt.maximalIdeal_eq_span_p]
  · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    intro h
    have hnorm :=
      (PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (-(2 : PadicA)) 2).mpr
        (by simpa [padicEisenstein] using h)
    have hnorm_two : ‖(2 : PadicA)‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
    rw [norm_neg, hnorm_two] at hnorm
    norm_num at hnorm

end ConcretePadicEisenstein
