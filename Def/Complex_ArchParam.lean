module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Inductive.LanglandsTunnell_RealArchParam
public import Structure.LanglandsTunnell_ArchParam

@[expose] public section

noncomputable section

namespace LanglandsTunnell

open Complex


def signShift (a : ZMod 2) : ℂ := if a = 0 then 0 else 1

namespace RealArchParam

def gammaR : RealArchParam → Multiset ℂ
  | principal u₁ a₁ u₂ a₂ => {u₁ + signShift a₁, u₂ + signShift a₂}
  | discrete _ _ _ => 0

def gammaC : RealArchParam → Multiset ℂ
  | principal _ _ _ _ => 0
  | discrete u k _ => {u + (k : ℂ) / 2}

def archFactor (P : RealArchParam) (s : ℂ) : ℂ :=
  (P.gammaR.map fun μ => Gammaℝ (s + μ)).prod * (P.gammaC.map fun ν => Gammaℂ (s + ν)).prod

def twist : RealArchParam → ℂ → ZMod 2 → RealArchParam
  | principal u₁ a₁ u₂ a₂, u, a => principal (u₁ + u) (a₁ + a) (u₂ + u) (a₂ + a)
  | discrete u₀ k hk, u, _ => discrete (u₀ + u) k hk

def dual : RealArchParam → RealArchParam
  | principal u₁ a₁ u₂ a₂ => principal (-u₁) a₁ (-u₂) a₂
  | discrete u k hk => discrete (-u) k hk

def centralExponent : RealArchParam → ℂ
  | principal u₁ _ u₂ _ => u₁ + u₂
  | discrete u _ _ => 2 * u

def centralSign : RealArchParam → ZMod 2
  | principal _ a₁ _ a₂ => a₁ + a₂
  | discrete _ k _ => (k : ZMod 2) + 1

end RealArchParam

namespace ComplexArchParam

def gammaC (P : ComplexArchParam) : Multiset ℂ :=
  {P.u₁ + (P.k₁.natAbs : ℂ) / 2, P.u₂ + (P.k₂.natAbs : ℂ) / 2}

def archFactor (P : ComplexArchParam) (s : ℂ) : ℂ :=
  (P.gammaC.map fun ν => Gammaℂ (s + ν)).prod

def twist (P : ComplexArchParam) (u : ℂ) (k : ℤ) : ComplexArchParam :=
  ⟨P.u₁ + u, P.k₁ + k, P.u₂ + u, P.k₂ + k⟩

def dual (P : ComplexArchParam) : ComplexArchParam :=
  ⟨-P.u₁, -P.k₁, -P.u₂, -P.k₂⟩

def centralExponent (P : ComplexArchParam) : ℂ := P.u₁ + P.u₂

def centralTwist (P : ComplexArchParam) : ℤ := P.k₁ + P.k₂

end ComplexArchParam

def RealArchParam.oddArtin : RealArchParam := .principal 0 0 0 1

def ComplexArchParam.trivialArtin : ComplexArchParam := ⟨0, 0, 0, 0⟩

end LanglandsTunnell

end

end
