/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/EgyptianFraction.lean -/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Def.NumberTheory.EgyptianFraction
public import Theorem.Nat.EgyptianFraction

@[expose] public section

namespace EgyptianFractionTest

def repeated : Fin 2 → ℕ := fun _ => 2

def increasing : Fin 2 → ℕ := fun i => i.val + 2

def decreasing : Fin 2 → ℕ := fun i => if i = 0 then 3 else 2

end EgyptianFractionTest
