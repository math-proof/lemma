-- Carved from Lemma/Definitions/Def_LanglandsTunnell_CubicInduction_HeckeRepresentatives.lean: instance decls only.
import Lemma.LanglandsTunnell.CubicInduction_Structure
import Lemma.LanglandsTunnell.CubicInduction_HeckeRepresentatives

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

noncomputable section


namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Hermite


section Residues

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicHaar
open NumberField.AdelicLevel LanglandsTunnell.CubicInduction HeckeIntegralSeam

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable instance finite_residueIndex : Finite (ResidueIndex v) :=
  Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

private noncomputable instance fintype_residueIndex : Fintype (ResidueIndex v) := Fintype.ofFinite _

end Residues

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Hermite


end
