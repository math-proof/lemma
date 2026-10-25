import Def.LanglandsTunnell_ConverseData

noncomputable section

namespace LanglandsTunnell

open Complex NumberField

namespace RealArchParam


end RealArchParam

namespace Converse

variable (K : Type) [Field K]


abbrev rsGammaR (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) : Multiset ℂ :=
  twistedGammaR K (archOfParamR K P) uR aR

abbrev rsGammaC (P : RealArchParam) (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) : Multiset ℂ :=
  twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC

end Converse

end LanglandsTunnell

end
