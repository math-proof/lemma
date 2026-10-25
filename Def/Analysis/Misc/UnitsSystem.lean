import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Theorem.Analysis.Misc.UnitsSystem
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- {given -show}`d, d', d₁, d₂` We will encounter a technical issue with Lean's type system, namely that the type {lean}`Scalar d`
and {lean}`Scalar d'` are not identical if {name}`d'` and {name}`d` are merely propositionally equal (as opposed
to definitionally equal); for instance, {lean}`Scalar (d₁+d₂)` and {lean}`Scalar (d₂+d₁)` are distinct types.
Technically, this renders multiplication on scalar types noncommutative. To get around this, we
create a casting operator, where the propositional equality is attempted to be resolved by the Lean
tactic {tactic}`module` whenever possible.  Unfortunately, the casting operator from {lean}`Scalar d` to {lean}`Scalar d'`
cannot be captured by standard Lean coercion classes such as {name}`Coe` or {name}`CoeOut` as each of the types
here contain parameters not present in the other. -/
def Scalar.cast {d d':Dimensions}  (q: Scalar d) (_ : d' = d := by module) : Scalar d' :=
  ⟨q.val⟩

end UnitsSystem
