module

public import Structure.LanglandsTunnell_ArchParam

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell

open Complex

def signEpsilon (a : ZMod 2) : ℂ := if a = 0 then 1 else I

def signShift (a : ZMod 2) : ℂ := if a = 0 then 0 else 1

namespace RealArchParam

def epsilonFactor : RealArchParam → ℂ
  | principal _ a₁ _ a₂ => signEpsilon a₁ * signEpsilon a₂
  | discrete _ k _ => I ^ (k + 1)

def gammaR : RealArchParam → Multiset ℂ
  | principal u₁ a₁ u₂ a₂ => {u₁ + signShift a₁, u₂ + signShift a₂}
  | discrete _ _ _ => 0

def gammaC : RealArchParam → Multiset ℂ
  | principal _ _ _ _ => 0
  | discrete u k _ => {u + (k : ℂ) / 2}

def twist : RealArchParam → ℂ → ZMod 2 → RealArchParam
  | principal u₁ a₁ u₂ a₂, u, a => principal (u₁ + u) (a₁ + a) (u₂ + u) (a₂ + a)
  | discrete u₀ k hk, u, _ => discrete (u₀ + u) k hk

def dual : RealArchParam → RealArchParam
  | principal u₁ a₁ u₂ a₂ => principal (-u₁) a₁ (-u₂) a₂
  | discrete u k hk => discrete (-u) k hk

end RealArchParam

namespace ComplexArchParam

def epsilonFactor (P : ComplexArchParam) : ℂ :=
  I ^ P.k₁.natAbs * I ^ P.k₂.natAbs

def gammaC (P : ComplexArchParam) : Multiset ℂ :=
  {P.u₁ + (P.k₁.natAbs : ℂ) / 2, P.u₂ + (P.k₂.natAbs : ℂ) / 2}

def twist (P : ComplexArchParam) (u : ℂ) (k : ℤ) : ComplexArchParam :=
  ⟨P.u₁ + u, P.k₁ + k, P.u₂ + u, P.k₂ + k⟩

def dual (P : ComplexArchParam) : ComplexArchParam :=
  ⟨-P.u₁, -P.k₁, -P.u₂, -P.k₂⟩

end ComplexArchParam

end LanglandsTunnell

end

end
