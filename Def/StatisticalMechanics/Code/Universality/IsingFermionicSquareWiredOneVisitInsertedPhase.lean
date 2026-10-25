/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitSplice
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExhaustive.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def carrierAdjacentSum {A : Type*} (f : A → A → Int) (l : List A) : Int :=
  (List.zipWith f l l.tail).sum

end
end StatMech.Universality
