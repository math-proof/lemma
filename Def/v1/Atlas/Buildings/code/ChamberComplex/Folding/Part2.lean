/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
import Structure.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part2
open scoped Classical

variable {V : Type*} [DecidableEq V]

variable {X : ChamberComplex V}


namespace Folding

namespace ReversibleFolding

variable (rf : ReversibleFolding X)

/-- The *wall* of a folding $f$: faces fixed pointwise by $f$ that lie in some moved chamber. -/
def Wall (X : ChamberComplex V) (f : Folding X) : Set (Finset V) :=
  {x | x ∈ X.toSimplicialComplex.faces ∧
       (∀ v ∈ x, f.morph.toFun v = v) ∧
       (∃ C, X.toSimplicialComplex.IsMaximal C ∧
              C.image f.morph.toFun ≠ C ∧ x ⊆ C)}

/-- The vertex-level reflection associated with a reversible folding: at each vertex, apply $g$
where $f$ fixes, and $f$ elsewhere. -/
def reflectionFun (rf : ReversibleFolding X) : V → V :=
  fun v => if rf.f.morph.toFun v = v then rf.g.morph.toFun v
           else rf.f.morph.toFun v

/-- Two chambers lie on *opposite* sides of the wall of $f$: one is fixed and the other moved. -/
def OppositeSides (f : Folding X) (C D : Finset V) : Prop :=
  (C.image f.morph.toFun = C ∧ D.image f.morph.toFun ≠ D) ∨
  (D.image f.morph.toFun = D ∧ C.image f.morph.toFun ≠ C)

/-- Two chambers lie on the *same* side of the wall of $f$: both fixed or both moved. -/
def SameSide (f : Folding X) (C D : Finset V) : Prop :=
  (C.image f.morph.toFun = C ∧ D.image f.morph.toFun = D) ∨
  (C.image f.morph.toFun ≠ C ∧ D.image f.morph.toFun ≠ D)

end ReversibleFolding
end Folding
