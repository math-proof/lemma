import Def.LanglandsTunnell_ConverseData
import Def.LanglandsTunnell_RankinSelbergEuler
import Structure.LocalLanglands_HeckeCosetSystem

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal
open LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Generators

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev LocalGL3 : Type := GL (Fin 3) (v.adicCompletion ℚ)

abbrev varpi : v.adicCompletion ℚ := (uniformizerUnit ℚ v : v.adicCompletion ℚ)

end Generators

section Eigen

variable {G : Type*} [Group G]

end Eigen

section Datum

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

end Datum

section BadPlaces

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

end BadPlaces

section UniformizerInverse

variable (v : HeightOneSpectrum (𝓞 ℚ))

end UniformizerInverse

end LanglandsTunnell.CubicInduction

end
