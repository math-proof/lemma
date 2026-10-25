/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotalDescentsParkingFunctions.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.TotalDescentsParkingFunctions


namespace MetaMathlibExt

-- descent predicate for one adjacent pair
abbrev descentPair (n : ℕ) (f : Fin n → Fin n) (p : Fin n × Fin n) : Prop :=
  p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2

abbrev adjPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1)

abbrev fiber (n : ℕ) (p : Fin n × Fin n) : Finset (Fin n → Fin n) :=
  (pfSet n).filter (fun f => descentPair n f p)

end MetaMathlibExt
