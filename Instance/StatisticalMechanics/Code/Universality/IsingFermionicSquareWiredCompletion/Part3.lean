/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part15


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable instance fkIsingSquareWiredBoundaryForwardDecidable
    (n : Nat) (hn : 0 < n) :
    DecidableRel (fkIsingSquareWiredBoundaryForward n hn) :=
  Classical.decRel _

noncomputable instance fkIsingSquareWiredBoundaryReverseDecidable
    (n : Nat) (hn : 0 < n) :
    DecidableRel (fkIsingSquareWiredBoundaryReverse n hn) :=
  Classical.decRel _


end
end StatMech.Universality
