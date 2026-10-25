/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Abbrev.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part4


noncomputable section

open CategoryTheory

universe u

namespace ChainHomotopy

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

def HomotopicChainMaps {C D : ChainComplexDef.ChainComplexRMod R} (f g : C ⟶ D) : Prop :=
  Nonempty (Homotopy f g)

end ChainHomotopy
end
