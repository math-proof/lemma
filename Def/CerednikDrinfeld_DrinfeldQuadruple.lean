import Mathlib
import Lemma.CerednikDrinfeld.FormalUpperHalfPlanePoints
import Structure.CerednikDrinfeld_DrinfeldQuadruple
import Abbrev.CerednikDrinfeld_DrinfeldQuadruple

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups
open LT.LatticeTree TensorProduct

namespace CerednikDrinfeld
namespace FormalOmega

section DetIndex

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]


end DetIndex

section Datum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]


theorem coe_smulInto_apply {N N' : Submodule 𝒪 (Fin 2 → K)} (h : ∀ v ∈ N, algebraMap 𝒪 K π • v ∈ N') (v : ↥N) :
    ((smulInto π h v : ↥N') : Fin 2 → K) = algebraMap 𝒪 K π • (v : Fin 2 → K) := rfl

variable (B) in


namespace DrinfeldDatum

variable {π}

def stratum₀ (Q : DrinfeldDatum (K := K) π B) : Set (PrimeSpectrum B) :=
  {x | LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁)}

def stratum₁ (Q : DrinfeldDatum (K := K) π B) : Set (PrimeSpectrum B) :=
  {x | LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀)}


def IsIsomorphic (Q Q' : DrinfeldDatum (K := K) π B) : Prop := Nonempty (Iso Q Q')

def IsQuadrupleOf (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B) : Prop :=
  ∀ x : PrimeSpectrum B,
    d.EdgeNondegAt π x.asIdeal (Q.L₀ x) (Q.L₁ x) ∧
    LinearMap.ker (Q.u₀ x) = (d.map π (toLocRing B x)).line (Q.L₀ x) ∧
    LinearMap.ker (Q.u₁ x) = (d.map π (toLocRing B x)).line (Q.L₁ x)

theorem IsQuadrupleOf.edge_iff (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B) (x : PrimeSpectrum B) :
    d.EdgeNondegAt π x.asIdeal (Q.L₀ x) (Q.L₁ x) ↔
    (Q.N₀ x ≤ Q.N₁ x ∧ (∀ v : ↥(Q.N₁ x), algebraMap 𝒪 K π • (v : Fin 2 → K) ∈ Q.N₀ x) ∧
      (∀ v : ↥(Q.N₁ x), (v : Fin 2 → K) ∉ Q.N₀ x →
        (1 : B) ⊗ₜ[𝒪] v ∉ d.line (Q.L₁ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₁ x)))) ∧
      (∀ v' : ↥(Q.N₀ x), (¬ ∃ w : ↥(Q.N₁ x), (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) →
        (1 : B) ⊗ₜ[𝒪] v' ∉ d.line (Q.L₀ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₀ x))))) :=
  Iff.rfl

end DrinfeldDatum

end Datum

end FormalOmega
end CerednikDrinfeld

end
