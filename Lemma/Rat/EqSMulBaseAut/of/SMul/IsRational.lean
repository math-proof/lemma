import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Lemma.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Lemma.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open AlgebraicCurve IsLocalRing
open Int


/--
[AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {σ : SemilinearAut K F}
  {v : AlgebraicCurve.Place K F}
  {f : F}
-- given
  (hv : v.IsRational)
  (hσv : (σ • v).IsRational) :
-- imply
  (σ • v).evalAt (σ • f) = SemilinearAut.baseAut σ (v.evalAt f) := by
-- proof
  classical
  by_cases hf : f ∈ v.toValuationSubring
  ·
    have hσf : σ • f ∈ (σ • v).toValuationSubring := by
      rw [SemilinearAut.smul_toValuationSubring]
      exact Set.smul_mem_smul_set hf
    apply (σ • v).algebraMap_residueField_injective
    rw [(σ • v).algebraMap_evalAt hσv hσf, ← SemilinearAut.smulResidueRingEquiv_algebraMap σ v,
      v.algebraMap_evalAt hv hf]
    show residue _ _ = IsLocalRing.ResidueField.mapEquiv _ (residue _ _)
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  ·
    have hσf : σ • f ∉ (σ • v).toValuationSubring := by
      rwa [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
    rw [Place.evalAt, Place.evalAt, dite_eq_right hσf, dite_eq_right hf, map_zero]


-- created on 2026-10-24
