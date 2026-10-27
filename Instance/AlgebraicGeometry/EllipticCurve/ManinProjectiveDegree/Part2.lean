import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
/-!
# Projective numerator degrees for Manin's proof

This file isolates the characteristic-free commutative algebra used to recover the numerator
degrees of two rational functions from primitive projective product and sum coordinates.
-/


namespace EllipticCurve.ManinProjectiveDegree

noncomputable section

open Polynomial

universe u

variable {K : Type u} [Field K]

instance : DecidableEq K := Classical.decEq K

instance : DecidableEq K[X] := Classical.decEq K[X]

end
end EllipticCurve.ManinProjectiveDegree
