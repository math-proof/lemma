/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding
open scoped Classical

variable {V : Type*} [DecidableEq V]

variable {X : ChamberComplex V}


namespace Folding

/-- A *reversible folding* is a pair $(f, g)$ of foldings such that $f$'s fixed chambers equal
$g$'s moved chambers (and vice versa), and the two foldings exchange the two boundary chambers
of any wall: $g(C) = C'$ where $C, C'$ are an adjacent fixed/moved pair under $f$. -/
structure ReversibleFolding (X : ChamberComplex V) where
  f : Folding X
  g : Folding X
  complementary_fixed : f.fixedChambers = g.movedChambers
  complementary_moved : f.movedChambers = g.fixedChambers
  opposite_action : ∀ C C',
    X.toSimplicialComplex.IsMaximal C →
    X.toSimplicialComplex.IsMaximal C' →
    C ≠ C' → C.image f.morph.toFun = C → C'.image f.morph.toFun = C →
    C.image g.morph.toFun = C'
  opposite_action' : ∀ C C',
    X.toSimplicialComplex.IsMaximal C →
    X.toSimplicialComplex.IsMaximal C' →
    C ≠ C' → C.image g.morph.toFun = C → C'.image g.morph.toFun = C →
    C.image f.morph.toFun = C'

end Folding
