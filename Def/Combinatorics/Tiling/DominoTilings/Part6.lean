import Mathlib
import Theorem.Combinatorics.Tiling.DominoTilings.Part4
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


def hasFaultAt (T : DominoTiling n m) (k : ℕ) : Prop :=
  k ≥ 1 ∧ k < n ∧ ∀ d ∈ T.dominos, ¬(d.minCol ≤ k ∧ k < d.maxCol)

end DominoTiling
end DominoTilings
