/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedPellNumbers.lean -/

import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum.Eq

namespace MetaMathlibExt

/-- Weight of a composition symbol: the two colors `0` and `1` of part one both
weigh one, while symbol `i ≥ 2` weighs `i`. -/
private def tccWt (k : ℕ) (a : Fin (k + 1)) : ℕ :=
  if a.val ≤ 1 then 1 else a.val

/-- Total weight of a list of composition symbols. -/
private def tccW (k : ℕ) (l : List (Fin (k + 1))) : ℕ :=
  (l.map (tccWt k)).sum

/-- All symbol lists of length at most `N`. -/
private def tccAll (k N : ℕ) : Finset (List (Fin (k + 1))) :=
  (Finset.range (N + 1)).biUnion fun ℓ =>
    ((Fintype.piFinset fun _ : Fin ℓ => (Finset.univ : Finset (Fin (k + 1)))).map
      ⟨List.ofFn, List.ofFn_injective⟩)

/-- Compositions of `n` as a finset of symbol lists. -/
private def tccFin (k n : ℕ) : Finset (List (Fin (k + 1))) :=
  (tccAll k n).filter fun l => tccW k l = n

/-- Weight on plain naturals, matching `tccWt` on valid symbols. -/
private def tccWn : ℕ → ℕ := fun j => if j ≤ 1 then 1 else j

/-- Contribution of head value `j` to the count. -/
private def tccPiece (k N : ℕ) (j : ℕ) : ℕ :=
  if tccWn j ≤ N then (tccFin k (N - tccWn j)).card else 0

/-- Compositions of `N` whose head symbol has value `j`. -/
private def tccHead (k N : ℕ) (j : ℕ) : Finset (List (Fin (k + 1))) :=
  (tccFin k N).filter fun l => l.head?.map Fin.val = some j
end MetaMathlibExt
