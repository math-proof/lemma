/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part2


namespace StatMech.FrontierA

open Finset

open scoped symmDiff

open StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamLeadingTerm (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
    grahamTwoPoint E J k m * grahamTwoPoint E J l m)


noncomputable def grahamKCorrection (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  -2 * (grahamBridgeGap E J i k m * grahamBridgeGap E J j k m *
    grahamTwoPoint E J k l)


noncomputable def grahamICorrection (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
    grahamBridgeGap E J i k m * grahamBridgeGap E J i l m)


noncomputable def grahamCorrectedRHS (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  grahamLeadingTerm E J i j k l m
    + grahamKCorrection E J i j k l m
    + grahamICorrection E J i j k l m


end StatMech.FrontierA
