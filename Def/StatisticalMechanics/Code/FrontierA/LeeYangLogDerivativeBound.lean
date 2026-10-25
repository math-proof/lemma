/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangFieldAnalytic.Part3
import Mathlib.Algebra.Polynomial.Splits
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLogDerivativeBound
open scoped BigOperators
open Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def leeYangNormalizedFieldLogDerivative
    (beta : ℝ) (h : ℂ) : ℂ :=
  leeYangComplexFieldLogDerivative G beta h / Fintype.card V

end StatMech.FrontierA
