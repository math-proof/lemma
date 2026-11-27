module

public import Mathlib
public import Def.ModularForm_HeckeOperator

public section

namespace ModularForm

axiom mdifferentiable_heckeT {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (heckeT k p f)

end ModularForm
