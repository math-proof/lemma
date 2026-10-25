/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc3_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc4_iteratecoincide
import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Def.StatisticalMechanics.Code.Walls.jc4_core
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc4_mergeDatum_of_reaches (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hne' : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e})
    (m m' n : ℕ)
    (hp : dartOrbitPeriod K a = m + n)
    (hp' : dartOrbitPeriod (K \ {r}) a' = m' + n)
    (hreach : (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1)
    (hconf : ∀ i, i < n → jc3_AvoidsEarFootprint r ((dartNext K)^[m + i] a.1))
    (hbal : jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 m) :
    jc4_MergeDatum K a r :=
  ⟨hne', a', m, m', n, hp, hp', hreach, hconf, hbal⟩


theorem jc4_splice_of_merge (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (h : jc4_MergeDatum K a r) : jc3_OrbitSpliceDatum K a r := by
  obtain ⟨hne', a', m, m', n, hp, hp', hmerge, hconf, hbal⟩ := h
  refine ⟨hne', a', m, m', n, hp, hp', ?_, hbal⟩
  intro i hi
  refine ⟨jc4_align_lockstep_bdd K a r a' m m' hmerge i (fun j hj => hconf j (hj.trans hi)),
          jc3_notProbed_of_avoidsEarFootprint r _ (hconf i hi)⟩


theorem jc4_merge_strengthens_splice (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) :
    jc4_MergeDatum K a r → jc3_OrbitSpliceDatum K a r :=
  jc4_splice_of_merge K a r


end Walls
end StatMech
