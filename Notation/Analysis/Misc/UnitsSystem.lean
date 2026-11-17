module

public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Def.Analysis.Misc.UnitsSystem.Part4

public section

set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- {given -show}`n : ℕ, d` One cannot use the Mathlib classes {name}`Pow` or {name}`HPow` here because the output type {lean}`Scalar (n • d)` depends on the input {name}`n`.  As the symbol {kw (of := «term_^_»)}`^` is reserved for such classes, we use the symbol `**` instead. -/
infix:80 "**" => Scalar.pow

end UnitsSystem
