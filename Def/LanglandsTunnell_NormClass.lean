import Def.Ideal_Main

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LanglandsTunnell.P2.Artin

open NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply

variable (K : Type*) [Field K] [NumberField K] (q : ℕ)

def normClass (v : HeightOneSpectrum (𝓞 K)) : (ZMod q)ˣ :=
  if h : Nat.Coprime (Ideal.absNorm v.asIdeal) q then ZMod.unitOfCoprime _ h else 1

def normClassChar {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) :
    NarrowRayClassGroup K 𝔣 →* (ZMod q)ˣ :=
  raySymbolDescend K (normClass K q) (normClassKillsRay K q hq𝔣)

end LanglandsTunnell.P2.Artin

end
