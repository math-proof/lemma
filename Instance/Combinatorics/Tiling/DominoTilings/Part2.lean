import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part6
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


instance (T : DominoTiling n m) (k : ℕ) : Decidable (T.hasFaultAt k) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))


end DominoTiling
end DominoTilings
