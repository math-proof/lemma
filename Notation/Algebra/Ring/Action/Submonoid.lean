import Mathlib.Algebra.Ring.Action.Submonoid

/-!
# FixedPoints additive-subgroup notation

Mathlib v4.30.0 `Mathlib/Algebra/Ring/Action/Submonoid.lean` declared
`α ^+ M` for `FixedPoints.addSubgroup M α`. v4.33.0 dropped the notation
line; the definition is unchanged. Re-declare it here so trees that still
write `α ^+ M` stay textual/semantic matches.
-/

notation α "^+" M:51 => FixedPoints.addSubgroup M α
