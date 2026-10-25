/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Theorem.v1.Atlas.TensorCategories.code.QBinomial
set_option maxHeartbeats 400000

variable {k : Type*} [Field k]


/-- The unnormalized q-factorial `qFactorial q m = ∏_{i<m} (q^{i+1} - 1)`. -/
noncomputable def qFactorial (q : k) (m : ℕ) : k :=
  ∏ i ∈ Finset.range m, (q ^ (i + 1) - 1)

/-- The q-falling factorial `qFallingFact q n m = ∏_{i<m} (q^{n-i} - 1)`. -/
noncomputable def qFallingFact (q : k) (n m : ℕ) : k :=
  ∏ i ∈ Finset.range m, (q ^ (n - i) - 1)

