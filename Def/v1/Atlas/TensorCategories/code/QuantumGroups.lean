/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Abbrev.v1.Atlas.TensorCategories.code.QuantumGroups
set_option maxHeartbeats 800000

universe u v


section QAnalogs

variable {k : Type*} [Field k]

/-- The q-analog `[n]_q = (q^n - q^{-n})/(q - q^{-1})` of a natural number `n`. -/
noncomputable def qAnalog (q : k) (n : ℕ) : k :=
  (q ^ n - q⁻¹ ^ n) / (q - q⁻¹)

/-- The q-analog factorial `[n]_q! = ∏_{l=1}^{n} [l]_q`. -/
noncomputable def qAnalogFactorial (q : k) (n : ℕ) : k :=
  ∏ l ∈ Finset.range n, qAnalog q (l + 1)

/-- The coefficient `(-1)^l / ([l]_q! · [N-l]_q!)` appearing in the q-Serre relations. -/
noncomputable def qSerreCoeff (q : k) (N l : ℕ) : k :=
  (-1) ^ l / (qAnalogFactorial q l * qAnalogFactorial q (N - l))

end QAnalogs
