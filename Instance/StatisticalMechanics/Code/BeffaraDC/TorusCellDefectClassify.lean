module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellComplement
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify.Part2
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


noncomputable local instance torusCellCutDualGraph_decidableRel
    (L : ℕ) [Fact (2 < L)] (S : Set (ZMod L × ZMod L)) :
    DecidableRel (torusCellCutDualGraph L S).Adj := Classical.decRel _

end StatMech.BeffaraDC
