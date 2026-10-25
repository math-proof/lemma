/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketeData.Part2
import Def.StatisticalMechanics.Code.FK.FKInterfaceSubadd
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false


namespace StatMech

namespace FK

section Interface

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]


structure fis_CrossInterface : Prop where
  
  le : (G ⊕g H) ≤ K
  
  inl : ∀ a b, K.Adj (Sum.inl a) (Sum.inl b) → G.Adj a b
  
  inr : ∀ c d, K.Adj (Sum.inr c) (Sum.inr d) → H.Adj c d

end Interface
end FK
end StatMech
