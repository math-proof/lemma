import Lemma.LanglandsTunnell.ArchParam

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell

open Complex

def signEpsilon (a : ZMod 2) : ℂ := if a = 0 then 1 else I


namespace RealArchParam

def epsilonFactor : RealArchParam → ℂ
  | principal _ a₁ _ a₂ => signEpsilon a₁ * signEpsilon a₂
  | discrete _ k _ => I ^ (k + 1)

end RealArchParam

namespace ComplexArchParam

def epsilonFactor (P : ComplexArchParam) : ℂ :=
  I ^ P.k₁.natAbs * I ^ P.k₂.natAbs

end ComplexArchParam

end LanglandsTunnell

end
