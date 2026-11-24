module
public import Mathlib
public import Lemma.Definitions.Def_AlgebraicCurve_AdelicIndex
public import Lemma.Definitions.Def_AlgebraicCurve_CanonicalDivisor
public import Theorem.Scheme.IsCurveOver
public import Def.AlgebraicCurve_RiemannRochRows
set_option autoImplicit false


public section

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]


theorem functionFieldRiemannRoch_of_riemann_and_duality
    (hWD : WeilDuality K F) : FunctionFieldRiemannRoch K F := by
  intro _ _ _ ω hω D
  linarith [hWD hω D]

theorem weilDuality_of_riemannIndex_of_adelic
    (hRI : RiemannIndexFormula K F) (hWD : WeilDualityAdelic K F) :
    WeilDuality K F := by
  intro _ _ _ ω hω D
  have h1 := hRI D
  have h2 := hWD hω D
  linarith

end AlgebraicCurve
end
