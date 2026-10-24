/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartitionSumBinomialCoefficient.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

open Finset

private noncomputable def wgt (m : ℕ) (k : Fin (m + 1) → ℕ) : ℕ :=
  ∑ i : Fin (m + 1), (i : ℕ) * k i

private noncomputable def summand (m : ℕ) (k : Fin (m + 1) → ℕ) : ℕ :=
  Nat.multinomial Finset.univ k * ∏ i : Fin (m + 1), (m.choose (i : ℕ)) ^ k i

-- Part B: nested binomial products

private noncomputable def suffixSum {m : ℕ} (s : Fin m → ℕ) (j : Fin m) : ℕ :=
  ∑ i : Fin m, if j < i then s i else 0

private noncomputable def nestProd {m : ℕ} (n : ℕ) (s : Fin m → ℕ) : ℕ :=
  ∏ j : Fin m, Nat.choose (n - suffixSum s j) (s j)

-- Part C: bijection between multinomial indices and target partitions

private noncomputable def tgt (m l : ℕ) : Type := Fin m → Fin (l + 1)

private noncomputable def tgtPred (m l : ℕ) (s : tgt m l) : Prop :=
  ∑ k : Fin m, ((k : ℕ) + 1) * ((s k : Fin (l + 1)) : ℕ) = l

private noncomputable def tgtValSum (m l : ℕ) (s : tgt m l) : ℕ :=
  ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ)

private noncomputable def tgtTerm (n m l : ℕ) (s : tgt m l) : ℕ :=
  ∏ k : Fin m,
    Nat.choose (n - ∑ i : Fin m, if k < i then (((s i : Fin (l + 1))) : ℕ) else 0)
      ((((s k : Fin (l + 1))) : ℕ)) *
    Nat.choose m ((k : ℕ) + 1) ^ ((((s k : Fin (l + 1))) : ℕ))

private noncomputable def fwd (m l : ℕ) (k : Fin (m + 1) → ℕ) : tgt m l :=
  fun j => ⟨min (k j.succ) l, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private noncomputable def bwd (n m l : ℕ) (s : tgt m l) : Fin (m + 1) → ℕ :=
  (Fin.cons (n - ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ))
    (fun j : Fin m => (((s j : Fin (l + 1))) : ℕ)) : Fin (m + 1) → ℕ)
private instance tgtFintype (m l : ℕ) : Fintype (tgt m l) := by unfold tgt; infer_instance

private instance tgtDecEq (m l : ℕ) : DecidableEq (tgt m l) := by unfold tgt; infer_instance

private instance decPredAnd (n m l : ℕ) :
    DecidablePred (fun s : tgt m l => tgtPred m l s ∧ tgtValSum m l s ≤ n) := by
  intro s
  unfold tgtPred tgtValSum
  infer_instance

private instance tgtSubtypeFintype (m l : ℕ) : Fintype (Subtype (tgtPred m l)) := by
  unfold tgtPred tgt
  infer_instance

private instance decPredSingle (m l : ℕ) :
    DecidablePred (fun s : tgt m l => tgtPred m l s) := by
  intro s
  unfold tgtPred
  infer_instance
end MetaMathlibExt
