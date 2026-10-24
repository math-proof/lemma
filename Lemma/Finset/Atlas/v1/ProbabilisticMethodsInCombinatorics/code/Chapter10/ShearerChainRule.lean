import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerChainRule
open Finset BigOperators ShannonEntropy Real ShearerEntropy


namespace ShearerEntropy

/--
[shannonEntropy_marginal_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerChainRule.lean)
-/
@[path]
lemma shannonEntropy_marginal_empty
  {n : ℕ}
  [Fintype Ω]
  [DecidableEq Ω]
  {p : PMF (Fin n → Ω)} :
-- imply
  shannonEntropy (marginal p ∅) = 0 := by
-- proof
  classical
  simp only [shannonEntropy]
  haveI : IsEmpty ↥(∅ : Finset (Fin n)) := Finset.instIsEmpty
  haveI : Unique (↥(∅ : Finset (Fin n)) → Ω) := Pi.uniqueOfIsEmpty _
  rw [Fintype.sum_unique]
  have h1 : (marginal p ∅) default = 1 := by
    have htsum := (marginal p ∅).tsum_coe
    rw [tsum_fintype, Fintype.sum_unique] at htsum
    exact_mod_cast htsum
  rw [h1, ENNReal.toReal_one, negMulLog_one]

end ShearerEntropy

namespace ShearerEntropy

/--
[shannonEntropy_marginal_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerChainRule.lean)
-/
@[path]
lemma shannonEntropy_marginal_univ
  {n : ℕ}
  [Fintype Ω]
  [DecidableEq Ω]
  {p : PMF (Fin n → Ω)} :
-- imply
  shannonEntropy (marginal p Finset.univ) = shannonEntropy p := by
-- proof
  classical
  have heq : marginal p Finset.univ = PMF.map (funUnivEquiv n Ω) p := by
    simp only [marginal, funUnivEquiv, PMF.map]
    rfl
  rw [heq, shannonEntropy_map_equiv]

end ShearerEntropy

namespace ShearerEntropy

/--
[filter_le_eq_filter_val_lt_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerChainRule.lean)
-/
@[path]
lemma filter_le_eq_filter_val_lt_succ
  {n : ℕ}
  [Fintype Ω]
  [DecidableEq Ω]
  {i : Fin n} :
-- imply
  Finset.filter (· ≤ i) (Finset.univ : Finset (Fin n)) = Finset.filter (fun j : Fin n => j.val < i.val + 1) Finset.univ := by
-- proof
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val]
  omega

end ShearerEntropy

namespace ShearerEntropy

/--
[filter_lt_eq_filter_val_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerChainRule.lean)
-/
@[path]
lemma filter_lt_eq_filter_val_lt
  {n : ℕ}
  [Fintype Ω]
  [DecidableEq Ω]
  {i : Fin n} :
-- imply
  Finset.filter (· < i) (Finset.univ : Finset (Fin n)) = Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ := by
-- proof
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]

end ShearerEntropy

namespace ShearerEntropy

/--
[chain_rule_telescoping](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerChainRule.lean)
-/
@[path]
lemma chain_rule_telescoping
  {n : ℕ}
  [Fintype Ω]
  [DecidableEq Ω]
  {p : PMF (Fin n → Ω)} :
-- imply
  shannonEntropy p = ∑ i : Fin n, (shannonEntropy (marginal p (Finset.filter (· ≤ i) Finset.univ)) - shannonEntropy (marginal p (Finset.filter (· < i) Finset.univ))) := by
-- proof
  classical
  let f : ℕ → ℝ := fun k =>
    shannonEntropy (marginal p (Finset.filter (fun j : Fin n => j.val < k) Finset.univ))
  have hterms : ∀ (i : Fin n),
    shannonEntropy (marginal p (Finset.filter (· ≤ i) Finset.univ)) -
    shannonEntropy (marginal p (Finset.filter (· < i) Finset.univ)) =
    f (i.val + 1) - f i.val := by
    intro i
    simp only [f]
    rw [filter_le_eq_filter_val_lt_succ i, filter_lt_eq_filter_val_lt i]
  simp_rw [hterms]
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i) n, Finset.sum_range_sub]
  have hf0 : f 0 = 0 := by
    show shannonEntropy (marginal p (Finset.filter (fun j : Fin n => j.val < 0) Finset.univ)) = 0
    have hempty : Finset.filter (fun j : Fin n => j.val < 0) Finset.univ = ∅ := by
      ext j; simp
    rw [hempty]
    exact shannonEntropy_marginal_empty p
  have hfn : f n = shannonEntropy p := by
    show shannonEntropy (marginal p (Finset.filter (fun j : Fin n => j.val < n) Finset.univ)) =
      shannonEntropy p
    have huniv : Finset.filter (fun j : Fin n => j.val < n) Finset.univ = Finset.univ := by
      ext j; simp
    rw [huniv]
    exact shannonEntropy_marginal_univ p
  linarith
/-- Lower bound on the entropy of the marginal restricted to $B$: summing the per-step
conditional entropy gains for $i \in B$ stays below $H(p|_B)$. Used to prove Shearer's lemma. -/

end ShearerEntropy


-- created on 2026-10-23
