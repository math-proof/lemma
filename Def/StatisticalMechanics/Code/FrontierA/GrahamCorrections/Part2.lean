/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections


namespace StatMech.FrontierA

open Finset

open scoped symmDiff

open StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamBridgeGap (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i k m : V) : ℝ :=
  grahamTwoPoint E J i k
    - grahamTwoPoint E J i m * grahamTwoPoint E J m k


end StatMech.FrontierA
