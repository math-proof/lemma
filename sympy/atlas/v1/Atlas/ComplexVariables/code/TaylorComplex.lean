/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/TaylorComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Complex Topology Filter Finset MeasureTheory

noncomputable def complexTaylorPoly (f : ℂ → ℂ) (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ range n, (iteratedDeriv k f a / (Nat.factorial k : ℂ)) * (z - a) ^ k
