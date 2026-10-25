/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveRouting.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictIncidence.Part2


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaDecoratedOrbitAtom.hasStrictPhysicalDoubleIncidence_cast
    (G : SimpleGraph V) (sites : I -> V)
    (A : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    {B C : Finset (LPReplicaCurrentVertex V)} (h : B = C)
    (z : LPReplicaDecoratedOrbitAtom G sites A B q) :
    LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites A C q
        (cast (congrArg
          (fun D => LPReplicaDecoratedOrbitAtom G sites A D q) h) z) ↔
      LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites A B q z := by
  subst C
  rfl

end
end StatMech.Ising
