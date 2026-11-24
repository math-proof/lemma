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
public import Theorem.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part3


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

omit [W.IsElliptic] in
noncomputable def autGroupEquivRootsOfUnity4
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha4 : W.a₄ ≠ 0) (ha6 : W.a₆ = 0) :
    autGroup F W ≃ rootsOfUnity 4 F :=
  Equiv.ofBijective
    (fun ⟨C, hC⟩ =>
      ⟨C.u, (mem_rootsOfUnity 4 C.u).mpr
        (autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC).1⟩)
    ⟨fun ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h => by
      have hu := congr_arg Subtype.val h
      simp only at hu
      have hd := autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC₁
      have hd2 := autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC₂
      exact Subtype.ext (VariableChange.ext hu
        (hd.2.1.trans hd2.2.1.symm)
        (hd.2.2.1.trans hd2.2.2.1.symm)
        (hd.2.2.2.trans hd2.2.2.2.symm)),
    fun ⟨ζ, hζ⟩ => by
      refine ⟨⟨⟨ζ, 0, 0, 0⟩, fourth_root_mem_autGroup ((mem_rootsOfUnity 4 ζ).mp hζ) ha6⟩, ?_⟩
      exact Subtype.ext rfl⟩

omit [W.IsElliptic] in
noncomputable def autGroupEquivRootsOfUnity6
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha6 : W.a₆ ≠ 0) (ha4 : W.a₄ = 0) :
    autGroup F W ≃ rootsOfUnity 6 F :=
  Equiv.ofBijective
    (fun ⟨C, hC⟩ =>
      ⟨C.u, (mem_rootsOfUnity 6 C.u).mpr
        (autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC).1⟩)
    ⟨fun ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h => by
      have hu := congr_arg Subtype.val h
      simp only at hu
      have hd := autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC₁
      have hd2 := autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC₂
      exact Subtype.ext (VariableChange.ext hu
        (hd.2.1.trans hd2.2.1.symm)
        (hd.2.2.1.trans hd2.2.2.1.symm)
        (hd.2.2.2.trans hd2.2.2.2.symm)),
    fun ⟨ζ, hζ⟩ => by
      refine ⟨⟨⟨ζ, 0, 0, 0⟩, sixth_root_mem_autGroup ((mem_rootsOfUnity 6 ζ).mp hζ) ha4⟩, ?_⟩
      exact Subtype.ext rfl⟩

def ArithmeticGeometry.SmoothProjectiveCurve.genus {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k) : ℕ := C.genusVal

def ArithmeticGeometry.SmoothProjectiveCurve.HasRationalPoint {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k) : Prop :=
  Nonempty C.RatPoint


end Theorem26_11
end WeierstrassCurve
end WeierstrassCurve.Affine.Point
end Theorem_23_16
end WeierstrassCurve
