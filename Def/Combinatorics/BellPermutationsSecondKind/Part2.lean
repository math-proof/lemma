/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.BellPermutationsSecondKind

@[expose] public section

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
