/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.LinearAlgebra.Lagrange
import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveComplete
import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete
import Theorem.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part2
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
