/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.HomologySequence
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section9.Part2
open CategoryTheory


namespace FiveLemma

variable {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type*}

variable [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
  [AddCommGroup A₄] [AddCommGroup A₅]

variable [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
  [AddCommGroup B₄] [AddCommGroup B₅]

attribute [instance] HomologyLadder.grpHA HomologyLadder.grpHB HomologyLadder.grpHC
  HomologyLadder.grpHA' HomologyLadder.grpHB' HomologyLadder.grpHC'

attribute [instance] LongExactLadder.grpA LongExactLadder.grpA' LongExactLadder.grpB
  LongExactLadder.grpB' LongExactLadder.grpC LongExactLadder.grpC'

namespace LongExactLadder

variable (L : LongExactLadder)

/-- Forgetting the subspace data: a map of pairs `(X, A) → (Y, B)` induces a map between
the trivial pairs `(X, ∅) → (Y, ∅)`. Used in the Eilenberg–Steenrod packaging. -/
def MapOfPairs.toSpaceMap {P Q : TopPair} (f : MapOfPairs P Q) :
    MapOfPairs (TopPair.ofSpace P.space) (TopPair.ofSpace Q.space) where
  toFun := f.toFun
  continuous_toFun := f.continuous_toFun
  mapsTo := fun _ h => h.elim

end LongExactLadder
end FiveLemma
