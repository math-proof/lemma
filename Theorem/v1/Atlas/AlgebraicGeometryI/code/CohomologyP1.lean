/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Int.Interval
import Def.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1
set_option maxHeartbeats 400000


namespace CohomologyP1

variable (k : Type) [Field k]


/-- `CechH0 k n` equals the submodule supported on the integer interval `[0, n]`. -/
theorem cechH0_eq_supported (n : ℤ) :
    CechH0 k n = Finsupp.supported k k (Set.Icc 0 n) := by
  simp only [CechH0, NonNeg, AtMost, ← Finsupp.supported_inter, Set.Ici_inter_Iic]

/-- The sum of the two chart submodules equals the submodule supported on
`Set.Ici 0 ∪ Set.Iic n`. -/
theorem sum_eq_supported (n : ℤ) :
    NonNeg k ⊔ AtMost k n = Finsupp.supported k k (Set.Ici 0 ∪ Set.Iic n) := by
  simp only [NonNeg, AtMost, ← Finsupp.supported_union]

/-- The set-theoretic complement of `Ici 0 ∪ Iic n` in `ℤ` is the open interval `Ioo n 0`. -/
lemma complement_union (n : ℤ) :
    (Set.Ici (0 : ℤ) ∪ Set.Iic n)ᶜ = Set.Ioo n 0 := by
  ext x; simp [Set.mem_Ioo]; omega

/-- The `k`-dimension of the submodule of finsupps supported on a finite set `S ⊆ ℤ` equals the
cardinality of `S`. -/
lemma finrank_supported_eq_card (S : Set ℤ) [Fintype S] :
    Module.finrank k ↥(Finsupp.supported k k S) = Fintype.card S := by
  rw [(Finsupp.supportedEquivFinsupp (R := k) (M := k) S).finrank_eq,
      Module.finrank_finsupp, Module.finrank_self, mul_one]


/-- `H^0(P^1, O(n)) = n + 1` for `n ≥ 0`. -/
theorem finrank_H0_nonneg (n : ℕ) :
    Module.finrank k ↥(CechH0 k ↑n) = n + 1 := by
  rw [cechH0_eq_supported, finrank_supported_eq_card]
  rw [← Set.toFinset_card, Set.toFinset_Icc, Int.card_Icc]
  simp

/-- For `n ≥ 0`, the two chart submodules sum to the entire space, so `H^1(P^1, O(n)) = 0`. -/
theorem H1_vanishes_nonneg (n : ℕ) :
    NonNeg k ⊔ AtMost k ↑n = ⊤ := by
  rw [sum_eq_supported, ← Finsupp.supported_univ]
  congr 1
  ext x; simp [Set.mem_Ici, Set.mem_Iic]; omega

/-- `H^1(P^1, O(n)) = 0` for `n ≥ 0`. -/
theorem finrank_H1_nonneg (n : ℕ) :
    Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k ↑n)) = 0 := by
  rw [H1_vanishes_nonneg]
  haveI : Subsingleton ((ℤ →₀ k) ⧸ (⊤ : Submodule k (ℤ →₀ k))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton


/-- For `n < 0`, `H^0(P^1, O(n)) = 0`. -/
theorem H0_vanishes_neg (n : ℤ) (hn : n < 0) :
    CechH0 k n = ⊥ := by
  rw [cechH0_eq_supported, ← Finsupp.supported_empty]
  congr 1
  ext x; simp [Set.mem_Icc]; omega

end CohomologyP1
