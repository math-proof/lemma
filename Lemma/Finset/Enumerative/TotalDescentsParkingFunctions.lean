import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.TotalDescentsParkingFunctions
open MetaMathlibExt


/--
[total_descents_over_parking_functions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotalDescentsParkingFunctions.lean)
-/
@[path]
private lemma total_descents_over_parking_functions_eq
  {n : ℕ} :
-- imply
  (∑ f : Fin n → Fin n,
    if IsParkingFunction n f
    then
    (Finset.univ.filter fun p : Fin n × Fin n =>
    p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2).card
    else 0) =
    Nat.choose n 2 * (n + 1) ^ (n - 2) := by
-- proof
  apply MetaMathlibExt.total_descents_over_parking_functions n


-- created on 2026-10-20
