/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ParkingFunction.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Def.Combinatorics.Enumerative.ParkingFunction


namespace MetaMathlibExt

instance (s t : ℕ) (f : Fin s → Fin t) :
    Decidable (IsPartialParkingFunction s t f) := by
  unfold IsPartialParkingFunction
  infer_instance

instance (n : ℕ) (f : Fin n → Fin n) : Decidable (IsParkingFunction n f) := by
  unfold IsParkingFunction
  infer_instance

end MetaMathlibExt
