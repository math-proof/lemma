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
import Def.GroupTheory.DicksonPGL2Wild.Part5
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

lemma mk_affineGL_gamma_lambda {F : Type*} [Field F] (g : borel F) :
    Matrix.ProjGenLinGroup.mk (affineGL (gamma g) (lambda g)) = g.1 := by
  classical
  let A := lift g.1
  have hA11 : A 1 1 ≠ 0 := lift_lowerRight_ne_zero g
  let u : Fˣ := Units.mk0 (A 1 1)⁻¹ (inv_ne_zero hA11)
  rw [← mk_lift g.1]
  symm
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨u, ?_⟩
  have hu : A * Matrix.GeneralLinearGroup.scalar (Fin 2) u =
      affineGL (gamma g) (lambda g) := by
    apply Units.ext
    simp only [Units.val_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, affineGL, u,
        gamma, lambda, A, lift_lowerLeft_eq_zero g, hA11, div_eq_mul_inv]
  exact hu

lemma toAff_injective {F : Type*} [Field F] : Function.Injective (toAff (F := F)) := by
  intro g h heq
  apply Subtype.ext
  rw [← mk_affineGL_gamma_lambda g, ← mk_affineGL_gamma_lambda h]
  have hgamma := congrArg (fun z : Aff F ↦ z.left.toAdd) heq
  have hlambda := congrArg (fun z : Aff F ↦ z.right) heq
  change gamma g = gamma h at hgamma
  change lambda g = lambda h at hlambda
  rw [hgamma, hlambda]

lemma toAff_surjective {F : Type*} [Field F] : Function.Surjective (toAff (F := F)) := by
  classical
  rintro ⟨a, u⟩
  let M := affineGL a.toAdd u
  have hMfix : M • (OnePoint.infty : OnePoint F) = OnePoint.infty := by
    apply OnePoint.smul_infty_eq_self_iff.mpr
    simp [M, affineGL]
  have hmem : Matrix.ProjGenLinGroup.mk M ∈ borel F := by
    apply MulAction.mem_stabilizer_iff.mpr
    have h := congrArg (OnePoint.equivProjectivization F) hMfix
    rw [OnePoint.equivProjectivization_smul] at h
    simpa [infinity] using h
  let g : borel F := ⟨Matrix.ProjGenLinGroup.mk M, hmem⟩
  refine ⟨g, ?_⟩
  have hmk : Matrix.ProjGenLinGroup.mk (lift g.1) = Matrix.ProjGenLinGroup.mk M := by
    exact mk_lift g.1
  have hM11 : (M : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    simp [M, affineGL]
  have hrat := ratios_eq_of_mk_eq (lift g.1) M hmk
    (lift_lowerRight_ne_zero g) hM11
  apply SemidirectProduct.ext
  · change gamma g = a.toAdd
    rw [show gamma g = (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 1 /
      lift g.1 1 1 by rfl, hrat.2]
    simp [M, affineGL]
  · apply Units.ext
    change (lambda g : F) = (u : F)
    rw [show (lambda g : F) = (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 0 /
      lift g.1 1 1 by rfl, hrat.1]
    simp [M, affineGL]

end DicksonWildAffine
end Dickson
end MetaMathlibExt
