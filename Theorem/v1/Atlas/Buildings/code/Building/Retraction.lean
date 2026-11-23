/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Retraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
public import Theorem.Finset.AgreeOnImage.of.AgreeOn
public import Theorem.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
public import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
open scoped Classical

public section

variable {V : Type*} [DecidableEq V]


