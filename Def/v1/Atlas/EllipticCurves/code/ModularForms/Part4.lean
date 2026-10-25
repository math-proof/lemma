/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.FermatsLastTheorem.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.FermatsLastTheorem
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Analytic.Order
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Finrank
import Abbrev.v1.Atlas.EllipticCurves.code.ModularForms.Part3
open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold


noncomputable section

namespace HeckeOperatorProperties

open Complex

/-- Coercion of a positive natural number `n` to a nonzero complex unit. -/
noncomputable def pnatToComplexUnits (n : ℕ+) : ℂˣ :=
  Units.mk0 (n : ℂ) (by exact_mod_cast n.ne_zero)

/-- The action of a nonzero complex scalar `l` on a complex lattice, scaling
both periods. -/
noncomputable def scaleLattice (l : ℂˣ) (L : ComplexLattice) : ComplexLattice where
  ω₁ := (l : ℂ) * L.ω₁
  ω₂ := (l : ℂ) * L.ω₂
  indep := by
    have hl : (l : ℂ) ≠ 0 := Units.ne_zero l
    let f : ℂ →ₗ[ℝ] ℂ := {
      toFun := fun x => (l : ℂ) * x
      map_add' := fun a b => by ring
      map_smul' := fun r x => Algebra.mul_smul_comm r (l : ℂ) x
    }
    have hf_ker : f.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at hx
      exact (mul_eq_zero.mp hx).resolve_left hl
    have heq : ![(l : ℂ) * L.ω₁, (l : ℂ) * L.ω₂] = f ∘ ![L.ω₁, L.ω₂] := by
      ext i; fin_cases i <;> simp [f]
    rw [heq]
    exact L.indep.map' f hf_ker

/-- The Hecke operator `T_n` acting on the free abelian group of lattices: sends
each lattice to the formal sum of its index-`n` sublattices. -/
noncomputable def homothetyR (l : ℂˣ) : Module.End ℤ DivL :=
  (FreeAbelianGroup.map (scaleLattice l)).toIntLinearMap

/-- The absolute Galois group of `ℚ`, `Gal(ℚ̄/ℚ)`. -/
noncomputable def reductionModL (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    GL (Fin 2) ℤ_[ℓ] →* GL (Fin 2) (ZMod ℓ) :=
  Matrix.GeneralLinearGroup.map PadicInt.toZMod

end HeckeOperatorProperties
end
