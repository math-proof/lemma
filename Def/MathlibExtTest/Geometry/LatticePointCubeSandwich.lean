/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/LatticePointCubeSandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.Geometry.LatticePointCubeSandwich.Part3
import Lemma.Set.LatticePointCubeSandwich
open LatticePointCubeSandwich MeasureTheory

/-!
# Tests for the bounded cubical measure sandwich

Concrete checks for `LatticePointCubeSandwich`:

- The half-open unit interval at `t = 1` meets the outer cube `0` but not
  cube `1`, and cube `0` is also inner.
- Direct uses of the inclusion, finiteness, and sandwich API on abstract
  bounded sets.
- The `n = 0` edge case.
-/


/-- The half-open unit interval as a `Fin 1` box. -/
noncomputable def halfOpenUnit : Set (Fin 1 → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)

