/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/EgyptianFraction.lean -/


import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Def.NumberTheory.EgyptianFraction
import Lemma.Nat.EgyptianFraction


namespace EgyptianFractionTest

def repeated : Fin 2 → ℕ := fun _ => 2

def increasing : Fin 2 → ℕ := fun i => i.val + 2

def decreasing : Fin 2 → ℕ := fun i => if i = 0 then 3 else 2

end EgyptianFractionTest
