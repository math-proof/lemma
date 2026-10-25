/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Def.StatisticalMechanics.Code.Universality.HexInjections.Part5


namespace StatMech.Universality

open Complex

open scoped BigOperators


theorem hexSplitAt_injective (cp : List ℤ → ℕ) :
    Function.Injective (hexSplitAt cp) := by
  intro s t h
  unfold hexSplitAt at h
  have h1 : (s.take (cp s), cp s) = (t.take (cp t), cp t) := (Prod.mk.injEq _ _ _ _).mp h |>.1
  have h2 : (s.drop (cp s), cp s) = (t.drop (cp t), cp t) := (Prod.mk.injEq _ _ _ _).mp h |>.2
  have htake : s.take (cp s) = t.take (cp t) := (Prod.mk.injEq _ _ _ _).mp h1 |>.1
  have hdrop : s.drop (cp s) = t.drop (cp t) := (Prod.mk.injEq _ _ _ _).mp h2 |>.1
  calc s = s.take (cp s) ++ s.drop (cp s) := (List.take_append_drop _ _).symm
    _ = t.take (cp t) ++ t.drop (cp t) := by rw [htake, hdrop]
    _ = t := List.take_append_drop _ _


end StatMech.Universality
