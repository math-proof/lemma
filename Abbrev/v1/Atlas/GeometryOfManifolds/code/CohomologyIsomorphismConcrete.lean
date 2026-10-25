/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Algebra.Module.Basic
open ContinuousAlternatingMap


/-- A (concrete) differential $n$-form on a normed space $E$: a smooth map assigning to each point an alternating continuous $n$-linear form. -/
abbrev DiffForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :=
  E → E [⋀^Fin n]→L[ℝ] ℝ

