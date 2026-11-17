/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
public import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
public import Structure.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3

@[expose] public section

open scoped Classical

variable {V : Type*} [DecidableEq V]

variable {X : ChamberComplex V}


namespace Folding

namespace ReversibleFolding

variable (rf : ReversibleFolding X)

namespace WallReflection

variable (s : WallReflection X)

/-- The reflection map of a wall reflection. -/
def refl : V → V := reflectionFun s.rf

/-- The wall (fixed set) of a wall reflection, viewed as a set of faces. -/
def wall : Set (Finset V) := Wall X s.rf.f

end WallReflection
end ReversibleFolding
end Folding
