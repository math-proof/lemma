/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupDefinition.Part2
open Polynomial AlgebraicGeometry


noncomputable section

namespace Blowup

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The underlying polynomial of `reesDecomposeComponent I f n` is the monomial of degree `n`
with coefficient `f.coeff n`. -/
lemma reesDecomposeComponent_coe_coe (f : reesAlgebra I) (n : ℕ) :
    ((reesDecomposeComponent I f n : ↥(reesAlgebra I)) : R[X]) =
    monomial n (f.val.coeff n) := rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- The `n`-th coefficient of the polynomial assembled from a direct-sum element coincides with
the `n`-th coefficient of the component in degree `n`. -/
lemma coeff_coeAddMonoidHom
    (x : DirectSum ℕ (fun n => ↥(reesGrading I n))) (n : ℕ) :
    ((DirectSum.coeAddMonoidHom (reesGrading I) x).val : R[X]).coeff n =
    ((x n).val : R[X]).coeff n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i xi =>
    simp only [DirectSum.coeAddMonoidHom_of]
    by_cases hin : i = n
    · subst hin; simp [DirectSum.of_eq_same]
    · have h1 := DirectSum.of_eq_of_ne
        (β := fun n => ↥(reesGrading I n)) i n xi (Ne.symm hin)
      rw [h1]; simp only [ZeroMemClass.coe_zero, coeff_zero]
      obtain ⟨a, ha, hxi⟩ := xi.property
      rw [hxi, coeff_monomial, if_neg hin]
  | add x y hx hy =>
    rw [map_add]
    have lhs_eq : ((DirectSum.coeAddMonoidHom (reesGrading I) x +
      DirectSum.coeAddMonoidHom (reesGrading I) y).val : R[X]) =
      (DirectSum.coeAddMonoidHom (reesGrading I) x).val +
      (DirectSum.coeAddMonoidHom (reesGrading I) y).val := rfl
    rw [lhs_eq, coeff_add, hx, hy]
    have rhs_eq : (((x + y) n).val : R[X]) =
      ((x n).val : R[X]) + ((y n).val : R[X]) := rfl
    rw [rhs_eq, coeff_add]

set_option synthInstance.maxHeartbeats 400000 in
/-- The graded pieces `reesGrading I n` form an internal direct sum decomposition of the Rees
algebra. -/
lemma reesGrading_isInternal : DirectSum.IsInternal (reesGrading I) := by
  constructor
  ·
    intro x y hxy
    ext n
    rename_i m
    obtain ⟨ax, hax, hxn⟩ := (x n).property
    obtain ⟨ay, hay, hyn⟩ := (y n).property
    rw [hxn, hyn, coeff_monomial, coeff_monomial]
    split_ifs with h
    · have hc := congr_arg (fun f => (f.val : R[X]).coeff n) hxy
      dsimp at hc
      rw [coeff_coeAddMonoidHom I x n, coeff_coeAddMonoidHom I y n] at hc
      simp only [hxn, hyn, coeff_monomial] at hc
      exact hc
    · rfl
  ·
    intro f
    use f.val.support.sum (fun n =>
      DirectSum.of (fun n => ↥(reesGrading I n)) n
        (reesDecomposeComponent I f n))
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, reesDecomposeComponent_coe_coe]
    exact (as_sum_support f.val).symm

/-- The multiplicative identity lies in the degree-zero piece of the Rees algebra. -/
theorem reesGrading_one_mem : (1 : reesAlgebra I) ∈ reesGrading I 0 := by
  refine ⟨1, ?_, ?_⟩
  · simp [Ideal.one_eq_top]
  · show (1 : reesAlgebra I).val = monomial 0 1
    simp

/-- Multiplication of homogeneous elements of degrees `i` and `j` lands in degree `i + j`. -/
theorem reesGrading_mul_mem {i j : ℕ} {fi fj : reesAlgebra I}
    (hi : fi ∈ reesGrading I i) (hj : fj ∈ reesGrading I j) :
    fi * fj ∈ reesGrading I (i + j) := by
  obtain ⟨a, ha, ha'⟩ := hi
  obtain ⟨b, hb, hb'⟩ := hj
  refine ⟨a * b, ?_, ?_⟩
  · rw [pow_add]; exact Ideal.mul_mem_mul ha hb
  · show (fi * fj : reesAlgebra I).val = monomial (i + j) (a * b)
    change fi.val * fj.val = _
    rw [ha', hb', monomial_mul_monomial]

end Blowup
end
