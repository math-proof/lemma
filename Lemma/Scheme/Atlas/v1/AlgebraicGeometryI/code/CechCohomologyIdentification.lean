import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CechCohomologyIdentification
open CechCohomologyIdentification


namespace CechCohomologyIdentification

/--
[serre_duality_from_cech_sheaf_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma serre_duality_from_cech_sheaf_data
  [Field k]
  {D : TateCechInfra.CechSheafData k} :
-- imply
  D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK :=
-- proof
  SerreDualityTate.serre_duality_from_tate_both D.setup D.curve D.deg
    D.h0_E D.h1_E D.h0_EK D.h1_EK
    D.hRR_E D.hRR_EK rfl rfl

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[serre_duality_h0_from_cech_sheaf_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma serre_duality_h0_from_cech_sheaf_data
  [Field k]
  {D : TateCechInfra.CechSheafData k} :
-- imply
  D.h0_EK = D.h1_E :=
-- proof
  (serre_duality_from_cech_sheaf_data D).1

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[serre_duality_h1_from_cech_sheaf_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma serre_duality_h1_from_cech_sheaf_data
  [Field k]
  {D : TateCechInfra.CechSheafData k} :
-- imply
  D.h0_E = D.h1_EK :=
-- proof
  (serre_duality_from_cech_sheaf_data D).2

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[serre_duality_unconditional_from_setup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma serre_duality_unconditional_from_setup
  [Field k]
  {S : SerreDualityTate.TateDualitySetup k}
  [FiniteDimensional k S.V]
  {C : CanonicalSheafCurves.SmoothCompleteCurve}
  {d : ℤ}
-- given
  (h0_E h1_EK : ℤ)
  (hRR_E : h0_E - ↑(Module.finrank k S.cechH1) = C.χ (1, d))
  (hRR_EK : ↑(Module.finrank k ↥S.dual.cechH0) - h1_EK = C.χ (1, C.degK - d)) :
-- imply
  ↑(Module.finrank k ↥S.dual.cechH0) = ↑(Module.finrank k S.cechH1) ∧ h0_E = h1_EK := by
-- proof
  constructor
  · exact_mod_cast SerreDualityTate.tate_duality_core S
  · have h_tate := SerreDualityTate.tate_duality_core S
    have h_chi := SerreDualityCurves.serre_duality_chi_rank1 C d
    have h_cast : (Module.finrank k ↥S.dual.cechH0 : ℤ) =
      (Module.finrank k S.cechH1 : ℤ) := by exact_mod_cast h_tate
    linarith

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[serre_duality_unconditional_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma serre_duality_unconditional_chi
  [Field k]
  {C : CanonicalSheafCurves.SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
-- proof
  SerreDualityCurves.serre_duality_chi_rank1 C d

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[serre_duality_other_direction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma serre_duality_other_direction
  [Field k]
  {C : CanonicalSheafCurves.SmoothCompleteCurve}
  {d : ℤ}
-- given
  (h0_E h1_E h0_EK h1_EK : ℤ)
  (hRR_E : h0_E - h1_E = C.χ (1, d))
  (hRR_EK : h0_EK - h1_EK = C.χ (1, C.degK - d))
  (hSD_one : h0_E = h1_EK) :
-- imply
  h1_E = h0_EK := by
-- proof
  have hchi := SerreDualityCurves.serre_duality_chi_rank1 C d
  linarith

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[serre_duality_other_direction_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma serre_duality_other_direction_reverse
  [Field k]
  {C : CanonicalSheafCurves.SmoothCompleteCurve}
  {d : ℤ}
-- given
  (h0_E h1_E h0_EK h1_EK : ℤ)
  (hRR_E : h0_E - h1_E = C.χ (1, d))
  (hRR_EK : h0_EK - h1_EK = C.χ (1, C.degK - d))
  (hSD_one : h1_E = h0_EK) :
-- imply
  h0_E = h1_EK := by
-- proof
  have hchi := SerreDualityCurves.serre_duality_chi_rank1 C d
  linarith

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[genus_equality_from_tate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma genus_equality_from_tate
  [Field k]
  {C : CanonicalSheafCurves.SmoothCompleteCurve}
-- given
  (h0_O h1_O h0_K h1_K : ℤ)
  (hRR_O : h0_O - h1_O = C.χ (1, 0))
  (hRR_K : h0_K - h1_K = C.χ (1, C.degK))
  (hSD : h0_O = h1_K) :
-- imply
  h1_O = h0_K := by
-- proof
  have hchi := SerreDualityCurves.serre_duality_chi_rank1 C 0
  simp only [sub_zero] at hchi
  linarith

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[deg_canonical_from_tate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma deg_canonical_from_tate
  [Field k]
  {C : CanonicalSheafCurves.SmoothCompleteCurve} :
-- imply
  C.degK = 2 * C.g - 2 :=
-- proof
  SerreDualityCurves.deg_K_from_serre_duality C

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[serre_duality_complete_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma serre_duality_complete_chain
  [Field k]
  {D : TateCechInfra.CechSheafData k} :
-- imply
  D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK ∧ D.curve.χ (1, D.deg) + D.curve.χ (1, D.curve.degK - D.deg) = 0 ∧ D.curve.χ (1, D.deg) = D.deg + 1 - D.curve.g := by
-- proof
  refine ⟨TateCechInfra.serre_duality_unconditional D,
    TateCechInfra.serre_duality_h0_eq_h1 D,
    SerreDualityCurves.serre_duality_chi_rank1 D.curve D.deg, ?_⟩
  rw [CanonicalSheafCurves.chi_eq_rr D.curve 1 D.deg]; ring

end CechCohomologyIdentification

namespace CechCohomologyIdentification

/--
[serre_duality_identification_is_rfl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyIdentification.lean)
-/
@[path]
lemma serre_duality_identification_is_rfl
  [Field k]
  {D : TateCechInfra.CechSheafData k} :
-- imply
  D.h0_EK = ↑(Module.finrank k ↥D.setup.dual.cechH0) ∧ D.h1_E = ↑(Module.finrank k D.setup.cechH1) :=
-- proof
  ⟨rfl, rfl⟩
end CechCohomologyIdentification



-- created on 2026-10-23
