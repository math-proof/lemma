/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotalDescentsParkingFunctions.lean -/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.TotalDescentsParkingFunctions

@[expose] public section


namespace MetaMathlibExt

-- descent predicate for one adjacent pair
abbrev descentPair (n : ℕ) (f : Fin n → Fin n) (p : Fin n × Fin n) : Prop :=
  p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2

abbrev adjPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1)

abbrev fiber (n : ℕ) (p : Fin n × Fin n) : Finset (Fin n → Fin n) :=
  (pfSet n).filter (fun f => descentPair n f p)

end MetaMathlibExt
