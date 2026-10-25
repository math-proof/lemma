/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Ramsey.lean -/


import Def.Combinatorics.Ramsey
import Lemma.Finset.Ramsey


namespace MathlibExt.Combinatorics.Ramsey

-- Faithful exact-statement exercise of the public theorem.
/-- The migrated finite two-uniform Ramsey theorem has the exact Wanted shape. -/
example {r k : ℕ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ φ : Finset (Fin N) → Fin r,
      ∃ S : Finset (Fin N), S.card = k ∧
        ∃ c : Fin r, ∀ T ∈ S.powersetCard 2, φ T = c :=
  ramsey_two_uniform hr

-- Boundary: asking for an empty homogeneous set always succeeds.
example {r : ℕ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ φ : Finset (Fin N) → Fin r,
      ∃ S : Finset (Fin N), S.card = 0 ∧
        ∃ c : Fin r, ∀ T ∈ S.powersetCard 2, φ T = c :=
  ramsey_two_uniform hr

-- Smoke: a single color forces every pair-set homogeneous.
example :
    ∃ N : ℕ, ∀ φ : Finset (Fin N) → Fin 1,
      ∃ S : Finset (Fin N), S.card = 3 ∧
        ∃ c : Fin 1, ∀ T ∈ S.powersetCard 2, φ T = c :=
  ramsey_two_uniform Nat.one_pos

end MathlibExt.Combinatorics.Ramsey
