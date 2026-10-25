/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part5
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrientedFourColorTag_leftPattern
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOrientedFourColorAtom G sites A B q) :
    LeftPattern (endsM (lpReplicaCurrentGraph G sites) z.1.1) Finset.univ
      A (B.map lpReplicaCurrentReflect.toEmbedding)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
      (lpReplicaTagFourColor G sites z.1.1
        (lpReplicaOrientedFourColorTag G sites A B q z)) := by
  rw [← lpReplicaRowGate_iff_leftPattern_tagFourColor]
  exact lpReplicaRowGate_orbitCollisionSplitTag
    G sites z.1.1 z.2.1.1 z.2.1.2 z.2.2.1.1
      (Finset.mem_filter.mp z.2.2.1.1.2).2
      z.2.2.2.1.1 z.2.2.2.2.1 A B
      z.2.2.2.1.2 z.2.2.2.2.2

end
end StatMech.Ising
