import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part10
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


instance (T : DominoTiling (n + 2) 2) : Decidable (hasVerticalFirstColumn T) := by
  unfold hasVerticalFirstColumn
  infer_instance


end DominoTiling
end DominoTilings
