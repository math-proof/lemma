import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.AlgorithmicLLL.Part2
open AlgorithmicLLL


namespace AlgorithmicLLL

/--
[outer_loop_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/AlgorithmicLLL.lean)
-/
@[path]
lemma outer_loop_nodup
  {sys : FixSystem Clause State}
  {sys : FixSystem Clause State}
  [DecidableEq Clause]
  {cs : List Clause}
  {s : State}
-- given
  (h : IsValidOuterLoop sys cs s) :
-- imply
  cs.Nodup := by
-- proof
  induction cs generalizing s with
  | nil => exact List.nodup_nil
  | cons c cs ih =>
    obtain ⟨hc_violated, hrest⟩ := h
    refine List.nodup_cons.mpr ⟨?_, ih (sys.fix c s) hrest⟩
    intro hc_mem
    have hc_sat : sys.satisfied c (sys.fix c s) := sys.fix_makes_satisfied c s
    suffices h_contra : ∀ (ds : List Clause) (s' : State),
      sys.satisfied c s' → IsValidOuterLoop sys ds s' → c ∉ ds by
      exact h_contra cs (sys.fix c s) hc_sat hrest hc_mem
    intro ds
    induction ds with
    | nil => intro _ _ _; exact List.not_mem_nil
    | cons d ds ih_ds =>
      intro s' hc_sat' ⟨hd_violated, hrest'⟩ hc_mem'
      cases List.mem_cons.mp hc_mem' with
      | inl heq =>
        rw [heq] at hc_sat'
        exact hd_violated hc_sat'
      | inr hc_in_ds =>
        have hc_sat'' : sys.satisfied c (sys.fix d s') :=
          sys.fix_preserves_satisfied d c s' hc_sat'
        exact ih_ds (sys.fix d s') hc_sat'' hrest' hc_in_ds

end AlgorithmicLLL

namespace AlgorithmicLLL

/--
[failureBound_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/AlgorithmicLLL.lean)
-/
@[path]
lemma failureBound_eq_pow
  {sys : FixSystem Clause State}
  {n k ℓ : ℕ} :
-- imply
  failureBound n k ℓ = 2 ^ (n + (ℓ * (k - 1) + 1)) := by
-- proof
  unfold failureBound numAssignments numExecutionTraces
  rw [← pow_add]

end AlgorithmicLLL

namespace AlgorithmicLLL

/--
[exponent_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/AlgorithmicLLL.lean)
-/
@[path]
lemma exponent_identity
  {sys : FixSystem Clause State}
  {n k ℓ : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  n + (ℓ * (k - 1) + 1) + ℓ = k * ℓ + (n + 1) := by
-- proof
  have h : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  nlinarith [Nat.sub_le k 1]

end AlgorithmicLLL

namespace AlgorithmicLLL

/--
[failure_prob_bound_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/AlgorithmicLLL.lean)
-/
@[path]
lemma failure_prob_bound_nat
  {sys : FixSystem Clause State}
  {n k ℓ : ℕ}
  {numFailing : ℕ}
-- given
  (h_inj : numFailing ≤ failureBound n k ℓ)
  (hk : 1 ≤ k) :
-- imply
  numFailing * 2 ^ ℓ ≤ 2 ^ (k * ℓ) * 2 ^ (n + 1) := by
-- proof
  have h_bound : numFailing ≤ 2 ^ (n + (ℓ * (k - 1) + 1)) := by
    rw [← failureBound_eq_pow]; exact h_inj
  calc numFailing * 2 ^ ℓ
    ≤ 2 ^ (n + (ℓ * (k - 1) + 1)) * 2 ^ ℓ := Nat.mul_le_mul_right _ h_bound
    _ = 2 ^ (n + (ℓ * (k - 1) + 1) + ℓ) := (pow_add 2 _ ℓ).symm
    _ = 2 ^ (k * ℓ + (n + 1)) := by
      congr 1
      exact exponent_identity n k ℓ hk
    _ = 2 ^ (k * ℓ) * 2 ^ (n + 1) := pow_add 2 _ _
/-- Theorem 6.6.6 (Moser's algorithm on $k$-CNF). Under the sharing condition
$\text{maxShared} \le 2^{k-3}$, the probability that Moser's `Fix` procedure makes more
than $\ell$ recursive calls is bounded by $2^{n+1}/2^\ell$, which decays geometrically in
$\ell$ and so the algorithm almost surely terminates. -/
end



-- created on 2026-10-23
