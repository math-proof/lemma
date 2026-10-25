/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part3


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}


noncomputable def bc19_glueFans [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (hRR : RA ∩ RB ⊆ S)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) :
    bc16_DisjointPathFamily G A B (Fin k) where
  a := FA.a
  b := fun i => FB.a (bc19_match hS FA FB i)
  p := bc19_gluedPath hS FA FB
  ha := FA.ha
  hb := fun i => FB.ha (bc19_match hS FA FB i)
  hp := bc19_gluedPath_isPath hS hRR FA FB
  hdisj := by
    intro i j hij z hzi hzj
    rw [bc19_gluedPath_support_mem] at hzi hzj
    rcases hzi with hiA | hiB <;> rcases hzj with hjA | hjB
    · exact FA.hdisj hij hiA hjA
    · exact hij (bc19_AFan_c_inj FA (bc19_cross_eq hS hRR FA FB hiA hjB))
    · exact hij (bc19_AFan_c_inj FA (bc19_cross_eq hS hRR FA FB hjA hiB)).symm
    · exact FB.hdisj ((bc19_match_inj hS FA FB).ne hij) hiB hjB


end StatMech.Walls
