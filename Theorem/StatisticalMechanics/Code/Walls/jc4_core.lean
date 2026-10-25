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
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc4_align_lockstep_bdd (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' : ℕ)
    (hmerge : (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1) (i : ℕ)
    (hconf : ∀ j, j < i → jc3_AvoidsEarFootprint r ((dartNext K)^[m + j] a.1)) :
    (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 := by
  induction i with
  | zero => simpa using hmerge
  | succ k ih =>
    have ihk := ih (fun j hj => hconf j (Nat.lt_succ_of_lt hj))
    rw [show m' + (k + 1) = (m' + k) + 1 by ring, show m + (k + 1) = (m + k) + 1 by ring,
        Function.iterate_succ_apply', Function.iterate_succ_apply', ihk]
    exact jc3_dartNext_eq_of_avoidsEarFootprint K r _ (hconf k (Nat.lt_succ_self k))


theorem jc4_align_lockstep (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' : ℕ)
    (hmerge : (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1)
    (hconf : ∀ j, jc3_AvoidsEarFootprint r ((dartNext K)^[m + j] a.1)) (i : ℕ) :
    (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 :=
  jc4_align_lockstep_bdd K a r a' m m' hmerge i (fun j _ => hconf j)


end Walls
end StatMech
