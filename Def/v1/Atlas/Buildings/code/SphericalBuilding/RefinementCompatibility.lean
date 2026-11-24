module
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.RefinementFrame
public import Theorem.Fin.SpacesVal.lt.SpacesAddVal1.of.IsStrictFlag
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Fintype.Fin


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementCompatibility.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The set of indices $\{j : j < i\}$ used to assemble $V_i$ from the first $i$ frame lines. -/
def sigmaWitness (i : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => j.val < i.val)

end GLnBuilding
