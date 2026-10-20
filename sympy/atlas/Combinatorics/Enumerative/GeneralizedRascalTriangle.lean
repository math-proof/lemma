/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GeneralizedRascalTriangle.lean -/

import Mathlib.Data.Int.Basic

/-!
# Generalized rascal triangle

Formalizes the required definition clause for the generalized rascal triangle
(concept `jis_sem_50bab0d7e77b4e96e0b23ce0`, statement `jis_3eaa558f60d302159fbb092e`).

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL23/Hotchkiss/hotchkiss4.tex>.
-/

namespace MetaMathlibExt

/-- A number triangle `T` is a generalized rascal triangle when there exist
integers `c`, `d`, `d₁`, `d₂` with `T r k = c + k * d₁ + r * d₂ + r * k * d`
for all `r, k ≥ 0` (concept `jis_sem_50bab0d7e77b4e96e0b23ce0`,
statement `jis_3eaa558f60d302159fbb092e`). -/
def IsGeneralizedRascalTriangle (T : ℕ → ℕ → ℤ) : Prop :=
  ∃ c d d₁ d₂ : ℤ, ∀ r k : ℕ,
    T r k = c + (k : ℤ) * d₁ + (r : ℤ) * d₂ + (r : ℤ) * (k : ℤ) * d

end MetaMathlibExt
