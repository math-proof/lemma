/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamImprovementBridge


namespace StatMech.FrontierA

open Finset

open scoped symmDiff

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamLeadingSurplus
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  grahamLeadingTerm E J i j k l m - grahamUrsell4 E J i j k l


noncomputable def grahamCorrectionDemand
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  -(grahamKCorrection E J i j k l m +
    grahamICorrection E J i j k l m)


end StatMech.FrontierA
