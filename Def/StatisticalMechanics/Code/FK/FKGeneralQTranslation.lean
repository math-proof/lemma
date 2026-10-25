/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech.FK

open StatMech.IsingFK

variable {d : ℕ}


noncomputable def fkgqt_transBoxMass (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) (p q : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb
    (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q)
    (flc_transEdges v N t m hNm)


end StatMech.FK
