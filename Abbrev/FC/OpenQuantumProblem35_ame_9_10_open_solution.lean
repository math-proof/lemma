/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open scoped BigOperators


namespace OpenQuantumProblem35

abbrev Config (n d : ℕ) := Fin n → Fin d


abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)


abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ


end OpenQuantumProblem35
