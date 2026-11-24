module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.LinearAlgebra.Lagrange
public import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveComplete
public import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
public import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete
public import Theorem.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u

attribute [instance] IsAlgebraicGroup.toIsTopologicalGroup

open WeierstrassCurve


namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (A B : R)

section Theorem_23_16

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

namespace WeierstrassCurve

section Theorem26_11

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsShortNF] [W.IsElliptic]

instance autGroup_finite (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Finite (autGroup F W) := by
  haveI : Finite (rootsOfUnity 12 F) := Finite.of_fintype _
  let f : autGroup F W → rootsOfUnity 12 F := fun C =>
    ⟨(C : VariableChange F).u,
     (mem_rootsOfUnity 12 _).mpr (autGroup_u_pow_twelve C.2 h2 h3)⟩
  apply Finite.of_injective f
  intro ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h
  have hu : C₁.u = C₂.u := congr_arg Subtype.val h
  exact Subtype.ext (VariableChange.ext hu
    (by rw [aut_r_eq_zero hC₁ h2 h3, aut_r_eq_zero hC₂ h2 h3])
    (by rw [aut_s_eq_zero hC₁ h2, aut_s_eq_zero hC₂ h2])
    (by rw [aut_t_eq_zero hC₁ h2 h3, aut_t_eq_zero hC₂ h2 h3]))

end Theorem26_11
end WeierstrassCurve
end WeierstrassCurve.Affine.Point
end Theorem_23_16
end WeierstrassCurve
