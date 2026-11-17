/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean -/

module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Structure.Combinatorics.Enumerative.MotzkinTriangle

@[expose] public section

/-!
# The Motzkin triangle as a Riordan array

This file records the formal-power-series description of the Motzkin triangle from Yassine
Otmani, *The 2-Pascal Triangle and a Related Riordan Array*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Otmani/otmani10.tex>.
-/


namespace MetaMathlibExt

namespace MotzkinRiordanPair

/-- The `(n, k)` entry of the Motzkin triangle represented by `p`. -/
noncomputable def entry (p : MotzkinRiordanPair) (n k : ℕ) : ℚ :=
  PowerSeries.coeff n (p.g * p.h ^ k)

end MotzkinRiordanPair

/-- The canonical Riordan pair defining the Motzkin triangle. -/
noncomputable def motzkinRiordanPair : MotzkinRiordanPair where
  g := motzkinG
  h := motzkinH
  isPair := ⟨motzkinSquareRoot, motzkinSquareRoot_isSquareRoot,
    motzkinG_mul_motzkinSquareRoot, two_mul_X_mul_motzkinH⟩

/-- The canonical `(n, k)` entry of the Motzkin triangle (OEIS A094531). -/
noncomputable def motzkinTriangle (n k : ℕ) : ℚ :=
  motzkinRiordanPair.entry n k

end MetaMathlibExt
