module

public import Mathlib
public import Def.NumberTheory.GeneralizedSylvester

public section

open Nat


namespace Nat

/--
[generalizedSylvester_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean)
-/
public theorem generalizedSylvester_zero
  {n : ℕ} :
-- imply
  generalizedSylvester n 0 = n + 1 :=
-- proof
  rfl

end Nat

namespace Nat

/--
[generalizedSylvester_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean)
-/
public theorem generalizedSylvester_succ
  {n k : ℕ} :
-- imply
  generalizedSylvester n (k + 1) =
      generalizedSylvester n k ^ 2 - generalizedSylvester n k + 1 :=
-- proof
  rfl

end Nat

namespace Nat

/--
[generalizedSylvester_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean)
-/
public theorem generalizedSylvester_pos
  {n k : ℕ} :
-- imply
  0 < generalizedSylvester n k := by
-- proof
  induction k with
  | zero => simp [generalizedSylvester]
  | succ k ih =>
    rw [generalizedSylvester]
    have ha : 0 < generalizedSylvester n k := ih
    have hsq : generalizedSylvester n k ≤ generalizedSylvester n k ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_self _
    omega

end Nat


-- created on 2026-10-20
-- updated on 2026-10-28
