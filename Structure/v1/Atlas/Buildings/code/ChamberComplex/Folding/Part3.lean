/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part2
open scoped Classical

variable {V : Type*} [DecidableEq V]

variable {X : ChamberComplex V}


namespace Folding

namespace ReversibleFolding

variable (rf : ReversibleFolding X)

/-- A *wall reflection*: a reversible folding equipped with the cross-fixing and cover axioms
needed to make its associated reflection a well-defined involution. -/
structure WallReflection (X : ChamberComplex V) where
  rf : ReversibleFolding X
  fg_id : ∀ v, rf.f.morph.toFun v = v → rf.f.morph.toFun (rf.g.morph.toFun v) = v
  gf_id : ∀ v, rf.g.morph.toFun v = v → rf.g.morph.toFun (rf.f.morph.toFun v) = v
  cover : ∀ v, rf.f.morph.toFun v = v ∨ rf.g.morph.toFun v = v

end ReversibleFolding
end Folding
