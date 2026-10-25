/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part5


namespace StatMech.Onsager

open BaseCase

def onsCyclicDirectionNonUturn (word : List (Fin 4)) : Prop :=
  List.IsChain onsDirectionNonUturn word ∧
    ∀ a ∈ word.getLast?, ∀ b ∈ word.head?, onsDirectionNonUturn a b


end StatMech.Onsager
