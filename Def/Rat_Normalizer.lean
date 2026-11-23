module

public import Theorem.Matrix.AdelicLevel
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Matrix
open Rat.HeightOneSpectrum Matrix.AdelicLevel

namespace RatIdele

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ


section Arch

def archCoord (x : (𝔸ℚ)ˣ) : ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace ((x : 𝔸ℚ).1 Rat.infinitePlace)

end Arch

section Order

def finPart : (𝔸ℚ)ˣ →* (𝔸ℚf)ˣ := Units.map (RingHom.snd (InfiniteAdeleRing ℚ) 𝔸ℚf).toMonoidHom

def ordAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : ℤ := -log (Valued.v ((x : 𝔸ℚ).2 v))

end Order

section Normalizer

def IsNormalizer (x : (𝔸ℚ)ˣ) (r : ℚ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((x : 𝔸ℚ).2 v) = v.valuation ℚ r) ∧ 0 < archCoord x * (r : ℝ)

def archSign (x : (𝔸ℚ)ˣ) : ℚ := if 0 < archCoord x then 1 else -1

def ρ (x : (𝔸ℚ)ˣ) : ℚ :=
  archSign x * ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ((natGenerator v : ℕ) : ℚ) ^ ordAt v x

end Normalizer

section UnitAt

def unitAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : v.adicCompletion ℚ :=
  (x : 𝔸ℚ).2 v * (algebraMap ℚ (v.adicCompletion ℚ) (ρ x))⁻¹

def unitIntAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : v.adicCompletionIntegers ℚ :=
  ⟨unitAt v x, (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (valued_unitAt v x).le⟩

end UnitAt

end RatIdele

end
