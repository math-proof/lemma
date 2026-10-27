import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.GeneralizedHypergeometric.Part3
open MetaMathlibExt.GeneralizedHypergeometric


/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_coefficient_zero_eq
-- given
  (K : Type*)
  [Field K]
  (a b : Multiset K) :
-- imply
  generalizedHypergeometricCoefficient a b 0 = 1 := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_zero a b

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_coefficient_empty_eq
-- given
  (K : Type*)
  [Field K]
  (n : ℕ) :
-- imply
  generalizedHypergeometricCoefficient (0 : Multiset K) 0 n = (n.factorial : K)⁻¹ := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_empty n

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_coefficient_cons_upper_eq
-- given
  (K : Type*)
  [Field K]
  (x : K)
  (a b : Multiset K)
  (n : ℕ) :
-- imply
  generalizedHypergeometricCoefficient (Multiset.cons x a) b n =
    (ascPochhammer K n).eval x * generalizedHypergeometricCoefficient a b n := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_cons_upper x a b n

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_coefficient_cons_lower_eq
-- given
  (K : Type*)
  [Field K]
  (a b : Multiset K)
  (x : K)
  (n : ℕ) :
-- imply
  generalizedHypergeometricCoefficient a (Multiset.cons x b) n =
    generalizedHypergeometricCoefficient a b n * ((ascPochhammer K n).eval x)⁻¹ := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_cons_lower a b x n

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_coefficient_cons_both_cancel_eq
-- given
  (K : Type*)
  [Field K]
  (x : K)
  (n : ℕ)
  (hx : (ascPochhammer K n).eval x ≠ 0)
  (a b : Multiset K) :
-- imply
  generalizedHypergeometricCoefficient (Multiset.cons x a) (Multiset.cons x b) n =
    generalizedHypergeometricCoefficient a b n := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_cons_both_cancel x a b n hx

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_coefficient_eq_zero_of_neg_coe_nat_mem_lower_eq
-- given
  (K : Type*)
  [Field K]
  (k n : ℕ)
  (b : Multiset K)
  (hk : k < n)
  (hmem : -(k : K) ∈ b)
  (a : Multiset K) :
-- imply
  generalizedHypergeometricCoefficient a b n = 0 := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_lower a b hk hmem

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_coefficient_eq_zero_of_zero_mem_lower_eq
-- given
  (K : Type*)
  [Field K]
  (n : ℕ)
  (b : Multiset K)
  (hn : 0 < n)
  (hmem : (0 : K) ∈ b)
  (a : Multiset K) :
-- imply
  generalizedHypergeometricCoefficient a b n = 0 := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_eq_zero_of_zero_mem_lower a b hn hmem

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_coefficient_eq_zero_of_neg_coe_nat_mem_upper_eq
-- given
  (K : Type*)
  [Field K]
  (k n : ℕ)
  (a : Multiset K)
  (hk : k < n)
  (hmem : -(k : K) ∈ a)
  (b : Multiset K) :
-- imply
  generalizedHypergeometricCoefficient a b n = 0 := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_upper a b hk hmem

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_coefficient_two_one_eq
-- given
  (K : Type*)
  [Field K]
  (a b c : K)
  (n : ℕ) :
-- imply
  generalizedHypergeometricCoefficient ({a, b} : Multiset K) {c} n =
    ordinaryHypergeometricCoefficient a b c n := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_two_one a b c n

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_series_apply_eq_eq
-- given
  (K : Type*)
  [Field K]
  (A : Type*)
  [Ring A]
  [Algebra K A]
  [TopologicalSpace A]
  [IsTopologicalRing A]
  (a b : Multiset K)
  (x : A)
  (n : ℕ) :
-- imply
  generalizedHypergeometricSeries (A := A) a b n (fun _ => x) =
    generalizedHypergeometricCoefficient a b n • x ^ n := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricSeries_apply_eq a b x n

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_series_apply_zero_eq
-- given
  (K : Type*)
  [Field K]
  (A : Type*)
  [Ring A]
  [Algebra K A]
  [TopologicalSpace A]
  [IsTopologicalRing A]
  (a b : Multiset K)
  (n : ℕ) :
-- imply
  generalizedHypergeometricSeries (A := A) a b n (fun _ => (0 : A)) =
    Pi.single (M := fun _ => A) 0 1 n := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricSeries_apply_zero a b n

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_series_two_one_eq
-- given
  (K : Type*)
  [Field K]
  (A : Type*)
  [Ring A]
  [Algebra K A]
  [TopologicalSpace A]
  [IsTopologicalRing A]
  (a b c : K) :
-- imply
  generalizedHypergeometricSeries (A := A) ({a, b} : Multiset K) {c} =
    ordinaryHypergeometricSeries A a b c := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricSeries_two_one a b c

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_value_eq_tsum_eq
-- given
  (a b : Multiset ℂ)
  (z : ℂ) :
-- imply
  generalizedHypergeometricValue a b z =
    ∑' n : ℕ, generalizedHypergeometricCoefficient a b n * z ^ n := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricValue_eq_tsum a b z

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_value_has_sum_is
-- given
  (a b : Multiset ℂ)
  (z : ℂ)
  (hsum : SummableHypergeometric a b z) :
-- imply
  HasSum (fun n : ℕ => generalizedHypergeometricCoefficient a b n * z ^ n)
    (generalizedHypergeometricValue a b z) := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricValue_hasSum hsum

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma lower_parameters_admissible_asc_pochhammer_ne_zero_is
-- given
  (bs : Multiset ℂ)
  (b : ℂ)
  (hadm : LowerParametersAdmissible bs)
  (hb : b ∈ bs)
  (n : ℕ) :
-- imply
  (ascPochhammer ℂ n).eval b ≠ 0 := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.lowerParametersAdmissible_ascPochhammer_ne_zero hadm hb n

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma lower_parameters_admissible_forall_mem_ne_zero_is
-- given
  (bs : Multiset ℂ)
  (hadm : LowerParametersAdmissible bs) :
-- imply
  ∀ b ∈ bs,
  ∀ n : ℕ,
    (ascPochhammer ℂ n).eval b ≠ 0 := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.lowerParametersAdmissible_forall_mem_ne_zero hadm

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma summable_hypergeometric_of_neg_coe_nat_mem_upper_is
-- given
  (N : ℕ)
  (a : Multiset ℂ)
  (hmem : (-(N : ℂ) ∈ a))
  (b : Multiset ℂ)
  (z : ℂ) :
-- imply
  SummableHypergeometric a b z := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.summableHypergeometric_of_neg_coe_nat_mem_upper hmem

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_tsum_eq_finset_sum_eq
-- given
  (N : ℕ)
  (a : Multiset ℂ)
  (hmem : (-(N : ℂ) ∈ a))
  (b : Multiset ℂ)
  (z : ℂ) :
-- imply
  (∑' n : ℕ, generalizedHypergeometricCoefficient a b n * z ^ n) =
    ∑ n ∈ Finset.range (N + 1), generalizedHypergeometricCoefficient a b n * z ^ n := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometric_tsum_eq_finset_sum hmem

/--
[GeneralizedHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean)
-/
@[path]
private lemma generalized_hypergeometric_value_terminating_eq_finset_sum_eq
-- given
  (N : ℕ)
  (a : Multiset ℂ)
  (hmem : (-(N : ℂ) ∈ a))
  (b : Multiset ℂ)
  (z : ℂ) :
-- imply
  generalizedHypergeometricValue a b z =
    ∑ n ∈ Finset.range (N + 1), generalizedHypergeometricCoefficient a b n * z ^ n := by
-- proof
  apply MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricValue_terminating_eq_finset_sum hmem


-- created on 2026-10-11
