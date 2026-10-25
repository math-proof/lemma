/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangZeroFree.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def leeYangComplexFieldMagnetizationNumerator
    (beta : ℝ) (h : ℂ) : ℂ :=
  ∑ s : ConfigSpace V,
    ((beta : ℂ) * (∑ v : V, spin s v)) *
      Complex.exp
        ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
          (beta : ℂ) * h * (∑ v : V, spin s v))

end StatMech.FrontierA
