import Mathlib
import Def.AlgebraicGeometry_TwoChartCechCupProduct
import Lemma.AlgebraicGeometry.TwoAffineOpenCoverKaehler
import Lemma.AlgebraicGeometry.TwoChartCechLaurentChart

set_option autoImplicit false

noncomputable section

universe u v w

namespace TwoChartCech.Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R) {ι : Type w} [Fintype ι]

def residueSum (Λ : ι → 𝒰.LaurentChart) : Ω[𝒰.A01⁄R] →ₗ[R] R := ∑ i, (Λ i).residue


def ResiduesVanishOnCoboundaries (Λ : ι → 𝒰.LaurentChart) : Prop :=
  LinearMap.range 𝒰.kaehler.cechDiff ≤ LinearMap.ker (𝒰.residueSum Λ)


def kaehlerTrace (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ) : 𝒰.kaehler.H1 →ₗ[R] R :=
  𝒰.kaehler.traceForm (𝒰.residueSum Λ) hv


def serrePairingInt (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ) :
    𝒰.kaehler.H0 →ₗ[R] 𝒰.structureSheaf.H1 →ₗ[R] R :=
  𝒰.kaehler.tracePairing (𝒰.residueSum Λ) hv

end TwoChartCech.Cover

end
