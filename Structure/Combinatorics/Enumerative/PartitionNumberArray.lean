/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartitionNumberArray.lean -/

import Mathlib.Data.Nat.Factorial.Basic
import Def.Combinatorics.Enumerative.PartitionNumberArray
/-!
# Partition number array (concept jis_sem_4bcead3a4bcda58a1d4dbb9f)
-/


namespace MetaMathlibExt

namespace PartitionNumberArray

/-- Partition multiplicity vector of `n`.
Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
structure PartitionMultiplicity (n : Nat) where
  /-- Exponent coordinates. Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`;
  source D3 `jis_352979520d341b10e3330dad`. -/
  vec : Fin n → Nat
  /-- Weighted-sum certificate. Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`;
  source D3 `jis_352979520d341b10e3330dad`. -/
  weighted : multWeightSum n vec = n

end PartitionNumberArray
end MetaMathlibExt
