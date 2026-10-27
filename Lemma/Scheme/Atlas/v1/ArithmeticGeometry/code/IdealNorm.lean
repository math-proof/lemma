import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.ArithmeticGeometry.code.IdealNorm
open Ideal
open NumberField


/--
[idealNorm_span_singleton_numberField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IdealNorm.lean)
-/
@[path]
lemma idealNorm_span_singleton_numberField
  [Field K]
  [NumberField K]
  {α : RingOfIntegers K} :
-- imply
  idealNorm (Ideal.span {α}) = Int.natAbs (Algebra.norm ℤ α) :=
-- proof
  Ideal.absNorm_span_singleton α


-- created on 2026-10-23
