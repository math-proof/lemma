/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPathSplice.Part2
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredLoopGraph_isAlternating_incidence
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredLoopGraph n hn omega).IsAlternating
      (fkIsingSquareWiredIncidenceGraph n) := by
  intro v w w' hne hvw hvw'
  rcases hvw with hi | ht <;> rcases hvw' with hi' | ht'
  · exact False.elim (hne (hi.2.2.trans hi'.2.2.symm))
  · simp only [fkIsingSquareWiredIncidenceGraph]
    constructor
    · intro _ hi''
      exact fkIsingSquareWiredIncidenceMate_ne_transitionMate n hn omega v
        hi''.1 hi''.2.1 (hi''.2.2.symm.trans ht')
    · intro _
      exact hi
  · simp only [fkIsingSquareWiredIncidenceGraph]
    constructor
    · intro hi''
      exfalso
      exact (fkIsingSquareWiredIncidenceMate_ne_transitionMate n hn omega v
        hi''.1 hi''.2.1) (hi''.2.2.symm.trans ht)
    · intro hnot
      exact False.elim (hnot hi')
  · exact False.elim (hne (ht.trans ht'.symm))


end
end StatMech.Universality
