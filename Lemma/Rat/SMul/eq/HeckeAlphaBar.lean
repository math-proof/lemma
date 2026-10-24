import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_HeckeOperator
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open ModularCurve AlgebraicCurve AlgebraicCurve.SemilinearAut IntermediateField HahnSeries
open Int


/--
[ModularCurve_arithmeticGalois_smul_heckeAlphaBar](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_arithmeticGalois_smul_heckeAlphaBar.lean)
-/
@[path]
private lemma main
  [Field L] [Algebra ℚ L]
  {N ℓ : ℕ} [NeZero N] [NeZero ℓ]
  {x : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N)}
-- given
  (σ : L ≃ₐ[ℚ] L) :
-- imply
  ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull (N * ℓ)) σ • (ModularCurve.heckeAlphaBar L N ℓ x) = ModularCurve.heckeAlphaBar L N ℓ (ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull N) σ • x) :=
-- proof
  Subtype.ext <|
    (coe_arithmeticGalois_smul (modularFunctionFieldFull (N * ℓ)) σ
        (heckeAlphaBar L N ℓ x)).trans <|
      ((congrArg (coeffMap (σ : L →+* L)) (coe_heckeAlphaBar N ℓ x)).trans
        ((coe_arithmeticGalois_smul (modularFunctionFieldFull N) σ x).symm.trans
          (coe_heckeAlphaBar N ℓ
            (arithmeticGalois (modularFunctionFieldFull N) σ • x)).symm))


-- created on 2026-10-24
