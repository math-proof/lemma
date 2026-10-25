import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.Correspondence
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open AlgebraicCurve
open scoped Pointwise
open Int


/--
[AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : Place K F}
-- given
  (σ : F ≃ₐ[K] F)
  (hσ : σ.toAlgHom.toRingHom.IsIntegral) :
-- imply
  v.restrictAlong σ.toAlgHom hσ = SemilinearAut.ofAlgAut σ.symm • v := by
-- proof
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  show σ x ∈ v.toValuationSubring ↔ _
  rfl


-- created on 2026-10-24
