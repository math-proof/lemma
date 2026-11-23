module

public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Def.Analysis.Misc.UnitsSystem.Part2
@[expose] public section

set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

noncomputable instance Scalar.instCoeFormal (d: Dimensions) : CoeOut (Scalar d) Formal where
  coe := toFormal

end UnitsSystem
