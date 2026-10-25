import Def.LanglandsTunnell_ConverseData

noncomputable section

namespace LanglandsTunnell

open Complex NumberField

namespace RealArchParam

def baseChange : RealArchParam → ComplexArchParam
  | principal u₁ _ u₂ _ => ⟨u₁, 0, u₂, 0⟩
  | discrete u k _ => ⟨u, (k : ℤ), u, -(k : ℤ)⟩

end RealArchParam

namespace Converse

variable (K : Type) [Field K]

def archOfParamR (P : RealArchParam) : ∀ w : InfinitePlace K, w.IsReal → RealArchParam :=
  fun _ _ => P

def archOfParamC (P : RealArchParam) : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam :=
  fun _ _ => P.baseChange

end Converse

end LanglandsTunnell

end
