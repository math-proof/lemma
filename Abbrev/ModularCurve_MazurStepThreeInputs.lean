import Def.ModularCurve_Eisenstein
import Def.ModularCurve_MazurStepThree

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable (p : ℕ) [NeZero p]

abbrev jBar : modularFunctionFieldBar p :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩

abbrev jpBar : modularFunctionFieldBar p :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩

end ModularCurve

namespace ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine

variable (p : ℕ) [NeZero p]

abbrev JQuot : Type :=
  (W : WeierstrassCurve ℤ) → ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →
    AlgebraicClosure ℚ

end ModularCurve

end
