module
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.UnitInterval
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section15.Part3
open Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SphereInfty

/-- The shift operator $T$ restricted to a continuous self-map of $S^{\infty}$. -/
def TOnSphere : C(Sphere, Sphere) where
  toFun x := ⟨T x.1, T_mem_sphere_set x⟩
  continuous_toFun := (continuous_T.comp continuous_subtype_val).subtype_mk _


end SphereInfty
