/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangZeroFree.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangFieldAnalytic.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def leeYangComplexFieldObservableNumerator
    (beta : ℝ) (f : ConfigSpace V → ℂ) (h : ℂ) : ℂ :=
  ∑ s : ConfigSpace V, f s * Complex.exp
    ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
      (beta : ℂ) * h * (∑ v : V, spin s v))

noncomputable def leeYangComplexFieldExpectation
    (beta : ℝ) (f : ConfigSpace V → ℂ) (h : ℂ) : ℂ :=
  leeYangComplexFieldObservableNumerator G beta f h /
    leeYangComplexFieldPartition G beta h

end StatMech.FrontierA
