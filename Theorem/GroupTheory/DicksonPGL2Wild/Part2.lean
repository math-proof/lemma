/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theorem.GroupTheory.DicksonPGL2Tame.Part4
import Lemma.Nat.Card_Stabilizer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Def.GroupTheory.DicksonPGL2Wild.Part4
/-!
# Dickson's classification in the wild case

This file classifies finite subgroups of `PGL₂` over an algebraic closure of an odd finite
field when the characteristic divides the group order. It also supplies the projective linear
group order formulas and characteristic-order element facts used by the classification.
-/


namespace MetaMathlibExt

namespace Dickson

open scoped BigOperators Pointwise Polynomial

namespace DicksonWildAffine

lemma ratios_eq_of_mk_eq {F : Type*} [Field F] (A B : GL (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0)
    (hB11 : (B : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    (A 0 0 / A 1 1 = B 0 0 / B 1 1) ∧
      (A 0 1 / A 1 1 = B 0 1 / B 1 1) := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hentry (i j : Fin 2) : A i j * (u : F) = B i j := by
    have hij := congrArg (fun M : GL (Fin 2) F ↦
      (M : Matrix (Fin 2) (Fin 2) F) i j) hu
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] using hij
  constructor
  · apply (div_eq_div_iff hA11 hB11).2
    rw [← hentry 1 1, ← hentry 0 0]
    ring
  · apply (div_eq_div_iff hA11 hB11).2
    rw [← hentry 1 1, ← hentry 0 1]
    ring

lemma lambda_mul {F : Type*} [Field F] (g h : borel F) :
    lambda (g * h) = lambda g * lambda h := by
  classical
  let A := lift g.1
  let B := lift h.1
  let C := lift (g * h).1
  have hmk : Matrix.ProjGenLinGroup.mk C = Matrix.ProjGenLinGroup.mk (A * B) := by
    dsimp [A, B, C]
    rw [mk_lift, map_mul, mk_lift, mk_lift]
  have hAB11 : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    have hvalue : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        A 1 1 * B 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, A, B,
        lift_lowerLeft_eq_zero g]
    rw [hvalue]
    exact mul_ne_zero (lift_lowerRight_ne_zero g) (lift_lowerRight_ne_zero h)
  have hrat := ratios_eq_of_mk_eq C (A * B) hmk
    (lift_lowerRight_ne_zero (g * h)) hAB11
  apply Units.ext
  change C 0 0 / C 1 1 = (A 0 0 / A 1 1) * (B 0 0 / B 1 1)
  rw [hrat.1]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show A 1 0 = 0 by exact lift_lowerLeft_eq_zero g,
    show B 1 0 = 0 by exact lift_lowerLeft_eq_zero h]
  simp only [zero_mul, zero_add]
  field_simp [lift_lowerRight_ne_zero g, lift_lowerRight_ne_zero h]
  ring

lemma gamma_mul {F : Type*} [Field F] (g h : borel F) :
    gamma (g * h) = gamma g + (lambda g : F) * gamma h := by
  classical
  let A := lift g.1
  let B := lift h.1
  let C := lift (g * h).1
  have hmk : Matrix.ProjGenLinGroup.mk C = Matrix.ProjGenLinGroup.mk (A * B) := by
    dsimp [A, B, C]
    rw [mk_lift, map_mul, mk_lift, mk_lift]
  have hAB11 : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    have hvalue : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        A 1 1 * B 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, A, B,
        lift_lowerLeft_eq_zero g]
    rw [hvalue]
    exact mul_ne_zero (lift_lowerRight_ne_zero g) (lift_lowerRight_ne_zero h)
  have hrat := ratios_eq_of_mk_eq C (A * B) hmk
    (lift_lowerRight_ne_zero (g * h)) hAB11
  change C 0 1 / C 1 1 = A 0 1 / A 1 1 + (A 0 0 / A 1 1) * (B 0 1 / B 1 1)
  rw [hrat.2]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show A 1 0 = 0 by exact lift_lowerLeft_eq_zero g]
  simp only [zero_mul, zero_add]
  have hA11 : A 1 1 ≠ 0 := lift_lowerRight_ne_zero g
  have hB11 : B 1 1 ≠ 0 := lift_lowerRight_ne_zero h
  field_simp [hA11, hB11]
  ring

lemma lambda_one {F : Type*} [Field F] : lambda (1 : borel F) = 1 := by
  have h := lambda_mul (1 : borel F) 1
  rw [one_mul] at h
  calc
    lambda (1 : borel F) = (lambda (1 : borel F))⁻¹ *
        (lambda (1 : borel F) * lambda (1 : borel F)) := by group
    _ = (lambda (1 : borel F))⁻¹ * lambda (1 : borel F) := by rw [← h]
    _ = 1 := by simp

lemma gamma_one {F : Type*} [Field F] : gamma (1 : borel F) = 0 := by
  have h := gamma_mul (1 : borel F) 1
  rw [one_mul, lambda_one] at h
  simp only [Units.val_one, one_mul] at h
  linear_combination -h

end DicksonWildAffine
end Dickson
end MetaMathlibExt
