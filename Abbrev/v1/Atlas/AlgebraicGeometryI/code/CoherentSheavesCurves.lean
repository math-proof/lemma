module
public import Structure.v1.Atlas.AlgebraicGeometryI.code.DegreeAdditivity
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.DegreeAdditivity
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckGroup
public import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup.Part3
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves
open scoped TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section Saturation

variable {R : Type*} [CommRing R] [IsDomain R]

variable {M : Type*} [AddCommGroup M] [Module R M]

open DegreeAdditivity in
/-- The Grothendieck group `K_0` of coherent sheaves on a curve, abbreviated through the abstract
construction `GrothendieckGroupK0`. -/
abbrev CoherentSheavesCurves.K0 (R : Type*) [Ring R] := GrothendieckGroupK0 R

open DegreeAdditivity in
/-- The class of an `R`-module `M` in the Grothendieck group `K_0(R)`. -/
abbrev CoherentSheavesCurves.K0.classOf (R : Type*) [Ring R] (M : ModuleCat R) :
    CoherentSheavesCurves.K0 R :=
  GrothendieckGroupK0.classOf R M

end Saturation
