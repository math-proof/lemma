import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Theorem.Analysis.Misc.UnitsSystem.Part14
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- We cannot use Mathlib's {name}`Inv` class here or the associated {kw (of := «term_⁻¹»)}`⁻¹` notation because {name}`Inv` requires the output to be of the same type as the input. -/
noncomputable def Scalar.inv {d:Dimensions} (q:Scalar d) : Scalar (-d) := ⟨ q.val⁻¹ ⟩

end UnitsSystem
