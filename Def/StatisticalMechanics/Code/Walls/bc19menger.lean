/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc19menger


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}


noncomputable def bc19_AFan_of_family {A S R : Set V}
    (F : bc16_DisjointPathFamily G A S (Fin k))
    (hreg : ∀ i, ∀ z ∈ (F.p i).support, z ∈ R) :
    bc19_AFan G A S R k := by
  have hhit : ∀ i, ∃ z ∈ (F.p i).support, z ∈ S :=
    fun i => ⟨F.b i, (F.p i).end_mem_support, F.hb i⟩
  choose c q hqpath hcS hqsub hqmeet using fun i => bc18_firstHitPath (F.p i) (hhit i)
  exact {
    a := F.a
    c := c
    q := q
    ha := F.ha
    hc := hcS
    hq := hqpath
    hmeet := hqmeet
    hreg := fun i z hz => hreg i z (hqsub i hz)
    hdisj := by
      intro i j hij z hzi hzj
      exact F.hdisj hij (hqsub i hzi) (hqsub j hzj) }


noncomputable def bc19_match [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) : Fin k → Fin k :=
  fun i => (bc19_AFan_c_cover hS FB (FA.c i) (FA.hc i)).choose

end StatMech.Walls
