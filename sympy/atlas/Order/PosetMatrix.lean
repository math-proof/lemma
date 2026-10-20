/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean -/

import Mathlib.Data.Matrix.Basic

namespace MetaMathlibExt

/-- Upper-triangular `(0, 1)`-poset matrix (concept `jis_sem_b6df1a00e0451f0892d6d4dd`):
a square Boolean matrix `M` over `Fin n` with false entries strictly below the
main diagonal (D2), true entries on the main diagonal (D3), and transitivity of
the true entries (D4): `M i j = true` and `M j k = true` imply `M i k = true`.

Source: JIS `mohammad3.tex`, lines 171–176, SHA-256
`839f29b85b01af033998ae2ca01fb12acb8b055b72ed095859474eb3f746a2b8`. -/
def IsPosetMatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) Bool) : Prop :=
  (∀ i j : Fin n, (j : ℕ) < (i : ℕ) → M i j = false) ∧
    (∀ i : Fin n, M i i = true) ∧
    (∀ i j k : Fin n, M i j = true → M j k = true → M i k = true)

/-- The order relation represented by a Boolean matrix (R1): `xᵢ ≤ xⱼ` iff the
`(i, j)`-entry is `true`. Defined separately from the poset-matrix predicate. -/
def IsPosetMatrix.Rel {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool)
    (i j : Fin n) : Prop :=
  M i j = true

/-- Projection of the upper-triangularity clause (D2). -/
theorem IsPosetMatrix.upper {n : ℕ} {M : Matrix (Fin n) (Fin n) Bool}
    (h : IsPosetMatrix n M) :
    ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → M i j = false :=
  h.1

/-- Projection of the diagonal clause (D3). -/
theorem IsPosetMatrix.diagonal {n : ℕ} {M : Matrix (Fin n) (Fin n) Bool}
    (h : IsPosetMatrix n M) : ∀ i : Fin n, M i i = true :=
  h.2.1

/-- Projection of the transitivity clause (D4). -/
theorem IsPosetMatrix.transitive {n : ℕ}
    {M : Matrix (Fin n) (Fin n) Bool} (h : IsPosetMatrix n M) :
    ∀ i j k : Fin n, M i j = true → M j k = true → M i k = true :=
  h.2.2

/-- The represented relation is reflexive. -/
theorem IsPosetMatrix.rel_refl {n : ℕ} {M : Matrix (Fin n) (Fin n) Bool}
    (h : IsPosetMatrix n M) (i : Fin n) :
    IsPosetMatrix.Rel M i i :=
  h.2.1 i

/-- The represented relation is transitive. -/
theorem IsPosetMatrix.rel_trans {n : ℕ} {M : Matrix (Fin n) (Fin n) Bool}
    (h : IsPosetMatrix n M) (i j k : Fin n)
    (hij : IsPosetMatrix.Rel M i j)
    (hjk : IsPosetMatrix.Rel M j k) :
    IsPosetMatrix.Rel M i k :=
  h.2.2 i j k hij hjk

end MetaMathlibExt
