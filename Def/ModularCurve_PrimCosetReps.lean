import Mathlib
import Instance.ModularCurve_PhiGen

set_option autoImplicit false

namespace ModularCurve

def primCosetReps (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.filter
    (fun t => t.1 * t.2.2 = N ∧ t.2.1 < t.2.2 ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1)
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1))


section Conjugates

variable {K : Type*} [Field K]

noncomputable def cosetConj (ζ : Kˣ) (J : LaurentSeries K) (t : ℕ × ℕ × ℕ) : LaurentSeries K :=
  if h : t.1 = 0 then 0 else
    haveI : NeZero t.1 := ⟨h⟩
    cosetSubst ζ t.1 t.2.1 J


noncomputable def cosetTwoVarPoly (ζ : Kˣ) (N : ℕ) (J : LaurentSeries K) : Polynomial (LaurentSeries K) :=
  (primCosetReps N).prod fun t => Polynomial.X - Polynomial.C (cosetConj ζ J t)

end Conjugates

end ModularCurve
