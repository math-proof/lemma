import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Additive.VanDerWaerdenAP
open scoped BigOperators Finset
open MetaMathlibExt


/--
[vanDerWaerden](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/VanDerWaerdenAP.lean)
-/
@[path]
private lemma vanDerWaerden_eq
  :
-- imply
  ∀ (r k : Nat), 0 < r → 0 < k →
    ∃ N : Nat, ∀ c : {m : Nat // 1 ≤ m ∧ m ≤ N} → Fin r, ∃ a d : Nat,
    1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ N ∧
    ∀ i : Nat, i < k → ∀ (h₁ : 1 ≤ a + i * d) (h₂ : a + i * d ≤ N)
    (h₀ : 1 ≤ a ∧ a ≤ N), c ⟨a + i * d, h₁, h₂⟩ = c ⟨a, h₀⟩ := by
-- proof
  apply MetaMathlibExt.vanDerWaerden


-- created on 2026-10-20
