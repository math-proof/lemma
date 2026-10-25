/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ExponentialPascalMatrix.lean -/

import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.PowerSeries.Exp
/-!
# Exponential Pascal-type matrices

The source identifies a family of exponential Riordan arrays represented by
`[e^t, t + r * t^2 / 2]`.  This file records both the generating-function pair and the
associated matrix.  Its `(n, k)` entry is

`n! / k! * [t^n] e^t * (t + r * t^2 / 2)^k`.

The parameter `r = 1` gives the Pascal-like matrix OEIS A100862, while `r = 2` gives the
example `[e^t, t + t^2]` from the source.

Source: Paul Barry, *Constructing Exponential Riordan Arrays from Their A and Z Sequences*,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Barry2/barry281.tex>.

JIS concept: `jis_sem_26c56e556549984950a493f3`.
-/


namespace MetaMathlibExt

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The second generating series `t + r * t^2 / 2` in the exponential Pascal-type pair. -/
noncomputable def exponentialPascalTypeSeries (r : ℚ) : PowerSeries R :=
  PowerSeries.X +
    PowerSeries.C (algebraMap ℚ R (r / 2)) * PowerSeries.X ^ 2

/-- The generating-function pair `[e^t, t + r * t^2 / 2]` for an exponential
Pascal-type matrix. -/
noncomputable def exponentialPascalTypePair (r : ℚ) : PowerSeries R × PowerSeries R :=
  (PowerSeries.exp R, exponentialPascalTypeSeries R r)

/-- The exponential Riordan matrix represented by `[e^t, t + r * t^2 / 2]`.

The factor `n! / k!` converts the coefficient of the `k`-th column's generating series
into the `(n, k)` matrix entry. -/
noncomputable def exponentialPascalTypeMatrix (r : ℚ) : Matrix ℕ ℕ R :=
  fun n k =>
    algebraMap ℚ R ((n.factorial : ℚ) / k.factorial) *
      (PowerSeries.exp R * (exponentialPascalTypeSeries R r) ^ k).coeff n

end MetaMathlibExt
