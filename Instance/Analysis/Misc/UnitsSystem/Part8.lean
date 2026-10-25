import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Theorem.Analysis.Misc.UnitsSystem.Part9
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

instance Scalar.instAddGroup {d:Dimensions} : AddGroup (Scalar d) :=
  val_injective _ |>.addGroup _ val_zero val_add val_neg val_sub (Function.swap val_smul) (Function.swap val_smul)

instance Scalar.instAddCommGroup {d:Dimensions} : AddCommGroup (Scalar d) :=
  val_injective _ |>.addCommGroup _ val_zero val_add val_neg val_sub (Function.swap val_smul) (Function.swap val_smul)

end UnitsSystem
