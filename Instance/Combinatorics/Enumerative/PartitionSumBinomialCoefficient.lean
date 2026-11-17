/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartitionSumBinomialCoefficient.lean -/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.PartitionSumBinomialCoefficient

@[expose] public section

namespace MetaMathlibExt

open Finset

instance tgtFintype (m l : ℕ) : Fintype (tgt m l) := by unfold tgt; infer_instance

instance tgtDecEq (m l : ℕ) : DecidableEq (tgt m l) := by unfold tgt; infer_instance

instance decPredAnd (n m l : ℕ) :
    DecidablePred (fun s : tgt m l => tgtPred m l s ∧ tgtValSum m l s ≤ n) := by
  intro s
  unfold tgtPred tgtValSum
  infer_instance

instance tgtSubtypeFintype (m l : ℕ) : Fintype (Subtype (tgtPred m l)) := by
  unfold tgtPred tgt
  infer_instance

instance decPredSingle (m l : ℕ) :
    DecidablePred (fun s : tgt m l => tgtPred m l s) := by
  intro s
  unfold tgtPred
  infer_instance

end MetaMathlibExt
