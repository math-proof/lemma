/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3
import Def.StatisticalMechanics.Code.Walls.bc19menger


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}


theorem bc19_match_spec [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) (i : Fin k) :
    FB.c (bc19_match hS FA FB i) = FA.c i :=
  (bc19_AFan_c_cover hS FB (FA.c i) (FA.hc i)).choose_spec

theorem bc19_match_inj [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) :
    Function.Injective (bc19_match hS FA FB) := by
  intro i j hij
  have h1 := bc19_match_spec hS FA FB i
  have h2 := bc19_match_spec hS FA FB j
  rw [hij] at h1
  exact bc19_AFan_c_inj FA (h1.symm.trans h2)


end StatMech.Walls
