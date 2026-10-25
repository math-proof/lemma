/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartitionSumBinomialCoefficient.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.PartitionSumBinomialCoefficient


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
