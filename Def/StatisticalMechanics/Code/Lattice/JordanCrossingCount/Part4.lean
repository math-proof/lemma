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
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part4
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

noncomputable def jcx_cross_P : PlanarZ2Subgraph where
  V := Fin 7
  finV := inferInstance
  decV := inferInstance
  G := jcx_cross_G
  emb := ⟨jcx_cross_emb, jcx_cross_emb_inj⟩
  isSub := jcx_cross_isSub


end Lattice
end StatMech
