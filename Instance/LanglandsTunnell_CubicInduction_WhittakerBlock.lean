-- Carved from Lemma/Definitions/Def_LanglandsTunnell_CubicInduction_WhittakerBlock.lean: instance decls only.
import Def.HaarQuotient
import Lemma.LanglandsTunnell.CubicInduction_Structure
import Lemma.NumberField.TateGlobalZeta
import Instance.M4aHerbrand_AdeleTopologyFacts

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicHaar LanglandsTunnell.CubicInduction Topology
open scoped ENNReal NNReal

namespace WhittakerBlock

instance sigmaCompactSpace_adelicGL3 : SigmaCompactSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI : SigmaCompactSpace (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (SigmaCompactSpace (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
  haveI : SigmaCompactSpace (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace


end WhittakerBlock

end
