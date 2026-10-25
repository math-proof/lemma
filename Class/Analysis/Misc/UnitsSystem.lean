import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
set_option doc.verso.suggestions false


/-! A framework to formalize units (such as length, time, mass, velocity, etc.) in Lean.
-/

/- Dimensions of units are measured by an additive group `Dimensions`, which will typically be a
free module inan group on a finite number of generators, representing fundamental units such as length,
mass, and time.  We bundle this together in a class `UnitsSystem`.  To use this system, we create
an instance of it, allowing in particular the additive group `Dimensions` to be accessed freely
within the `UnitsSystem` namespace.

I am no longer actively maintaining this code, and others are welcome to incorporate it into their own units implementations.  Existing units implications in Lean include

- https://github.com/ATOMSLab/LeanDimensionalAnalysis/tree/main
- https://github.com/ecyrbe/lean-units
- https://github.com/HEPLean/PhysLean/tree/master/PhysLean/Units

and a general discussion of how to implement units can be found at

https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units
-/

class UnitsSystem where
  Dimensions: Type*
  addCommGroup: AddCommGroup Dimensions

