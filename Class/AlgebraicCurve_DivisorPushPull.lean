import Lemma.AlgebraicCurve.DivisorPushPull

/-!
Re-export full Divisor push/pull / FundamentalIdentity / SumRamificationInertia API.

TEMP: Definitions still hosts the non-`class` fiber/ramification surface; Class keeps this
module as the import path many Def/Structure/Definitions files already use.
When Def owns `Place.fiber` / push-pull, switch this file to `import Def.…` and keep only classes.

Needed so `Class.lean` can also import `Class.ModularCurve_GaussPencilAdapter` (which
transitively pulls Definitions `Def_AlgebraicCurve_DivisorPushPull`) without duplicating
`AlgebraicCurve.SumRamificationInertia` from the former Class stubs.
-/
