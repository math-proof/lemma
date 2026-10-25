/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerODE
import Theorem.StatisticalMechanics.Code.SLE.LoewnerProps.Part3
open Complex Set Filter Topology
open scoped NNReal ComplexConjugate


namespace StatMech.SLE

def MonotoneHullFamily (K : ℝ → Set ℂ) : Prop :=
  (∀ t, IsCompactHull (K t)) ∧ Monotone K


end StatMech.SLE
