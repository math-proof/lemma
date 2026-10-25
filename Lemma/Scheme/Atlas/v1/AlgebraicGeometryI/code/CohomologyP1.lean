import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
open CohomologyP1


namespace CohomologyP1

/--
[H0_O_neg1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
lemma H0_O_neg1
  {k : Type}
  [Field k] :
-- imply
  CechH0 k (-1) = ⊥ :=
-- proof
  H0_vanishes_neg k (-1) (by norm_num)

end CohomologyP1

namespace CohomologyP1

/--
[finrank_H1_O_neg1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
lemma finrank_H1_O_neg1
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k (-1))) = 0 := by
-- proof
  have := finrank_H1_neg k (-1) (by norm_num : (-1 : ℤ) < 0)
  simpa using this

end CohomologyP1

namespace CohomologyP1

/--
[finrank_H1_O_neg2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
lemma finrank_H1_O_neg2
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k (-2))) = 1 := by
-- proof
  have := finrank_H1_neg k (-2) (by norm_num : (-2 : ℤ) < 0)
  simpa using this

end CohomologyP1

/--
[cechH0_eq_supported](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
private lemma cechH0_eq_supported_eq
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  CechH0 k n = Finsupp.supported k k (Set.Icc 0 n) := by
-- proof
  apply CohomologyP1.cechH0_eq_supported k n

/--
[sum_eq_supported](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
private lemma sum_eq_supported_eq
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  NonNeg k ⊔ AtMost k n = Finsupp.supported k k (Set.Ici 0 ∪ Set.Iic n) := by
-- proof
  apply CohomologyP1.sum_eq_supported k n

/--
[complement_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
private lemma complement_union_eq
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (Set.Ici (0 : ℤ) ∪ Set.Iic n)ᶜ = Set.Ioo n 0 := by
-- proof
  apply CohomologyP1.complement_union k n

/--
[finrank_supported_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
private lemma finrank_supported_eq_card_eq
  {k : Type}
  [Field k]
  {S : Set ℤ}
  [Fintype S] :
-- imply
  Module.finrank k ↥(Finsupp.supported k k S) = Fintype.card S := by
-- proof
  apply CohomologyP1.finrank_supported_eq_card k S

/--
[finrank_H0_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
private lemma finrank_H0_nonneg_eq
  {k : Type}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank k ↥(CechH0 k ↑n) = n + 1 := by
-- proof
  apply CohomologyP1.finrank_H0_nonneg k n

/--
[H1_vanishes_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
private lemma H1_vanishes_nonneg_eq
  {k : Type}
  [Field k]
  {n : ℕ} :
-- imply
  NonNeg k ⊔ AtMost k ↑n = ⊤ := by
-- proof
  apply CohomologyP1.H1_vanishes_nonneg k n

/--
[finrank_H1_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
private lemma finrank_H1_nonneg_eq
  {k : Type}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k ↑n)) = 0 := by
-- proof
  apply CohomologyP1.finrank_H1_nonneg k n

/--
[H0_vanishes_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
private lemma H0_vanishes_neg_eq
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  CechH0 k n = ⊥ := by
-- proof
  apply CohomologyP1.H0_vanishes_neg k n hn

/--
[finrank_H1_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean)
-/
@[path]
private lemma finrank_H1_neg_eq
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (_ : n < 0) :
-- imply
  Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) = (-n - 1).toNat := by
-- proof
  apply CohomologyP1.finrank_H1_neg k n _


-- created on 2026-10-23
