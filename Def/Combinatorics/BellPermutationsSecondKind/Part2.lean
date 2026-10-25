/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.BellPermutationsSecondKind


namespace MetaMathlibExt

/-! ## Part A: `bellPerm` is injective on RGFs -/

/-- Partial product of the first `m` swaps. -/
def pp {n : ℕ} (f : Fin n → Fin n) (m : ℕ) : Equiv.Perm (Fin n) :=
  (((List.finRange n).take m).map (fun i => Equiv.swap i (f i))).prod

/-! ## Part B: `numWeak (bellPerm f) = numVals f` -/

/-- Suffix product of the swaps with index `≥ m`. -/
def qq {n : ℕ} (f : Fin n → Fin n) (m : ℕ) : Equiv.Perm (Fin n) :=
  (((List.finRange n).drop m).map (fun i => Equiv.swap i (f i))).prod

end MetaMathlibExt
