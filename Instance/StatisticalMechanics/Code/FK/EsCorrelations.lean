/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.EsCorrelations.Part2
open scoped BigOperators

set_option linter.style.show false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


instance instDecidableConnected (ω : ConfigSpace (Sym2 V)) (x y : V) :
    Decidable (Connected G ω x y) :=
  inferInstanceAs (Decidable ((openSub G ω).Reachable x y))

instance instDecidablePredConnected (x y : V) :
    DecidablePred (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y) :=
  fun ω => instDecidableConnected G ω x y


end FK
end StatMech
