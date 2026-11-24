module
public import Mathlib
public import Def.Combinatorics.Tiling.DominoTilings.Part10
open Finset BigOperators


public section

namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


instance (T : DominoTiling (n + 2) 2) : Decidable (hasVerticalFirstColumn T) := by
  unfold hasVerticalFirstColumn
  infer_instance


end DominoTiling
end DominoTilings
