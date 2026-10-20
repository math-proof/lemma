import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.ParisHarrington
open MathlibExt.Combinatorics.ParisHarringtonWanted


/--
[paris_harrington](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ParisHarrington.lean)
-/
@[path]
private lemma paris_harrington_eq
  :
-- imply
  ∀ c k m : ℕ, 0 < c → 0 < k → 0 < m → ∃ N : ℕ,
    ∀ f : Finset ℕ → Fin c,
    ∃ H : Finset ℕ, ∃ hH : H.Nonempty,
    H ⊆ Finset.Icc 1 N ∧
    m ≤ H.card ∧
    H.min' hH ≤ H.card ∧
    ∃ t : Fin c, ∀ S : Finset ℕ, S ⊆ H → S.card = k → f S = t := by
-- proof
  apply MathlibExt.Combinatorics.ParisHarringtonWanted.paris_harrington


-- created on 2026-10-20
