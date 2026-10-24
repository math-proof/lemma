import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Complexity
open TuringMachine


namespace TuringMachine

/--
[IsBigO.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Complexity.lean)
-/
@[path]
lemma IsBigO.trans
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {f g h : ℕ → ℕ}
-- given
  (hfg : IsBigO f g)
  (hgh : IsBigO g h) :
-- imply
  IsBigO f h := by
-- proof
  obtain ⟨c₁, n₁, hc₁, hfg⟩ := hfg
  obtain ⟨c₂, n₂, hc₂, hgh⟩ := hgh
  refine ⟨c₁ * c₂, max n₁ n₂, Nat.mul_pos hc₁ hc₂, fun n hn => ?_⟩
  have h1 := hfg n (le_of_max_le_left hn)
  have h2 := hgh n (le_of_max_le_right hn)
  calc f n ≤ c₁ * g n := h1
    _ ≤ c₁ * (c₂ * h n) := Nat.mul_le_mul_left c₁ h2
    _ = c₁ * c₂ * h n := by rw [Nat.mul_assoc]

end TuringMachine


-- created on 2026-10-23
