/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Lean.Elab.Tactic.Omega


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {E K : Type*} [Fintype E] [DecidableEq E]


noncomputable def isoradialCriticalMu (theta : Real) : Complex :=
  Complex.I * (Real.tan theta : Complex)


end StatMech.FrontierA
