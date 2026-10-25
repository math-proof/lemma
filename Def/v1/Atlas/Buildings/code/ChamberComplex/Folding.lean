/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
import Structure.v1.Atlas.Buildings.code.ChamberComplex.Folding
open scoped Classical

variable {V : Type*} [DecidableEq V]

variable {X : ChamberComplex V}


namespace Folding

/-- The set of chambers fixed (as sets) by the folding $f$, i.e. $f(C) = C$. -/
def fixedChambers (f : Folding X) : Set (Finset V) :=
  {C | X.toSimplicialComplex.IsMaximal C ∧ C.image f.morph.toFun = C}

/-- The set of chambers moved by the folding $f$, i.e. $f(C) \neq C$. -/
def movedChambers (f : Folding X) : Set (Finset V) :=
  {C | X.toSimplicialComplex.IsMaximal C ∧ C.image f.morph.toFun ≠ C}

end Folding
