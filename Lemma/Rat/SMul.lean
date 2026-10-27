import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open scoped Pointwise
open Int


/--
[AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : AlgebraicCurve.Place K F}
-- given
  (σ : F ≃ₐ[K] F) :
-- imply
  AlgebraicCurve.SemilinearAut.ofAlgAut σ • v = σ • v := by
-- proof
  have hfun : ∀ x : F, AlgebraicCurve.SemilinearAut.ofAlgAut σ • x = σ • x := fun _ => rfl
  apply AlgebraicCurve.Place.toValuationSubring_injective
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, AlgebraicCurve.Place.smul_toValuationSubring,
    ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  simp only [hfun]


-- created on 2026-10-24
