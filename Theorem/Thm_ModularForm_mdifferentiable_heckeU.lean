module

public import Mathlib
public import Def.ModularForm_HeckeOperator

public section

namespace ModularForm

axiom mdifferentiable_heckeU {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (heckeU k p f)

end ModularForm
