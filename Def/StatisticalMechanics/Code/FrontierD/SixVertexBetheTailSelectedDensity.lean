/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailSelectedDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailCauchy


namespace StatMech.FrontierD

noncomputable section

open Filter Topology

def sixVertexHalfFilledBetheRootDataRecast
    {c : Real} (hc : 2 < c) (k : Nat) :
    {p : Fin ((k + (k + 1)) + 1) → Real //
      SixVertexOpenRootSimplex p ∧
        SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
          ((k + (k + 1)) + 1) p} := by
  let hcount : (k + (k + 1)) + 1 = (k + 1) + (k + 1) := by omega
  exact hcount.symm ▸
    ⟨sixVertexHalfFilledBetheRoots hc k,
      sixVertexHalfFilledBetheRoots_mem_open hc k,
      sixVertexHalfFilledBetheRoots_is_solution hc k⟩

def sixVertexHalfFilledBetheRootsRecast
    {c : Real} (hc : 2 < c) (k : Nat) :
    Fin ((k + (k + 1)) + 1) → Real :=
  (sixVertexHalfFilledBetheRootDataRecast hc k).1

def sixVertexSelectedFiniteRootDensity
    {c : Real} (hc : 2 < c) (k : Nat) : Real → Real :=
  sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
    ((k + (k + 1)) + 1) (sixVertexHalfFilledBetheRootsRecast hc k)

end
end StatMech.FrontierD
