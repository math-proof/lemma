/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/QPochhammer.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
/-!
# Infinite q-Pochhammer products

This file defines the complex infinite q-Pochhammer symbol and proves its
convergence on the open unit disk.

The raw product `qPochhammerInfRaw` is the total `tprod` value, which is `1` by
convention when the factor family is not multipliable. The canonical symbol
`qPochhammerInf` additionally takes convergence evidence `‖q‖ < 1`, so an
out-of-domain `q` cannot be passed silently.

## Main definitions

* `MetaMathlibExt.QPochhammer.qPochhammerInfRaw`
* `MetaMathlibExt.QPochhammer.qPochhammerInf`

## Main statements

* `MetaMathlibExt.QPochhammer.hasProd_qPochhammerInf`
* `MetaMathlibExt.QPochhammer.qPochhammerInfRaw_two_one`
-/


namespace MetaMathlibExt.QPochhammer

/-- Raw complex infinite q-Pochhammer product `(a;q)_∞`, total in `q`.

This is Mathlib's `tprod` over `ℕ` of the zero-based factor family
`1 - a * q ^ n`. When the factors are not multipliable (in particular for most
`q` with `‖q‖ ≥ 1`), `tprod` takes its conventional default value `1`; see
`qPochhammerInfRaw_two_one`. Use the canonical `qPochhammerInf`, which requires
convergence evidence `‖q‖ < 1`, unless this fallback behaviour is intended. -/
noncomputable def qPochhammerInfRaw (a q : ℂ) : ℂ :=
  tprod (fun n : ℕ => (1 - a * q ^ n))

/-- Complex infinite q-Pochhammer symbol `(a;q)_∞`, restricted to the unit disk.

Source `2607.10576:D01` / `2608.13818:D02` jointly define
`(a;q)_∞ := ∏_{j=0}^{∞} (1 - a·q^j)` for complex `a, q` with `‖q‖ < 1`.
On this domain the value agrees with the raw product `qPochhammerInfRaw a q`,
while the hypothesis `hq` makes it impossible to silently evaluate at an
out-of-domain `q`. -/
noncomputable def qPochhammerInf (a q : ℂ) (_hq : ‖q‖ < 1) : ℂ :=
  qPochhammerInfRaw a q

end MetaMathlibExt.QPochhammer
