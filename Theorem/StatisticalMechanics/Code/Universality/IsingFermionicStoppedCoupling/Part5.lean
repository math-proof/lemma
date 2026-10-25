/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem prodBits_injective_full
    {a b : List (Bool × Bool)}
    (hx : a.map Prod.fst = b.map Prod.fst)
    (hy : a.map Prod.snd = b.map Prod.snd) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons z b => simp at hx
  | cons z a ih =>
      cases b with
      | nil => simp at hx
      | cons w b =>
          simp only [List.map_cons, List.cons.injEq] at hx hy
          have hzw : z = w := Prod.ext hx.1 hy.1
          subst w
          congr 1
          exact ih hx.2 hy.2

end
end StatMech.Universality
