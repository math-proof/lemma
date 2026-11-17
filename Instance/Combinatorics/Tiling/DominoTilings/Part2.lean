module

public import Mathlib
public import Def.Combinatorics.Tiling.DominoTilings.Part6

@[expose] public section

open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


instance (T : DominoTiling n m) (k : ℕ) : Decidable (T.hasFaultAt k) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))


end DominoTiling
end DominoTilings
