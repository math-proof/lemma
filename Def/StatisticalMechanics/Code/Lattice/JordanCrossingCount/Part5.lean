module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
public import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part5
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def jcx_cross_cycB : jcx_cross_G.Walk 2 2 :=
  Walk.cons (by rw [jcx_cross_G_adj]; decide : jcx_cross_G.Adj 2 4)
    (Walk.cons (by rw [jcx_cross_G_adj]; decide : jcx_cross_G.Adj 4 5)
      (Walk.cons (by rw [jcx_cross_G_adj]; decide : jcx_cross_G.Adj 5 6)
        (Walk.cons (by rw [jcx_cross_G_adj]; decide : jcx_cross_G.Adj 6 2) Walk.nil)))

end Lattice
end StatMech
