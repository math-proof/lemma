import Mathlib
import Def.CerednikDrinfeld_DrinfeldQuadruple
import Structure.CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups
open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld
namespace FormalOmega
namespace DrinfeldDatum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

section BaseChange

variable {B' : Type} [CommRing B'] [Algebra 𝒪 B']


def IsBaseChangeAlong (f : B →ₐ[𝒪] B') (Q : DrinfeldDatum (K := K) π B) (Q' : DrinfeldDatum (K := K) π B') : Prop :=
  Nonempty (BaseChangeAlong f Q Q')

end BaseChange

section Translate


def IsTranslateEven (g : GL (Fin 2) K) (c : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Prop :=
  Nonempty (TranslateEven g c Q Q')


def IsTranslateOdd (g : GL (Fin 2) K) (c₀ c₁ : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Prop :=
  Nonempty (TranslateOdd g c₀ c₁ Q Q')

def Iso.toTranslateEven {Q Q' : DrinfeldDatum (K := K) π B} (e : Iso Q Q') : TranslateEven 1 1 Q Q' where
  N₀_eq x := by rw [scalarGL_one, one_mul, inv_one, latticeMap_one]; exact (e.N₀_eq x).symm
  N₁_eq x := by rw [scalarGL_one, one_mul, inv_one, latticeMap_one]; exact (e.N₁_eq x).symm
  τ₀ := e.τ₀
  τ₁ := e.τ₁
  τ₁_Pi₀ := e.τ₁_Pi₀
  τ₀_Pi₁ := e.τ₀_Pi₁
  τ₀_u₀ x v hv hv' := by
    have h1 : ((scalarGL (1 : Kˣ) * (1 : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
      rw [scalarGL_one, one_mul, inv_one, Units.val_one, Matrix.one_mulVec]
    have hv'' : v ∈ Q'.N₀ x := by rw [← h1]; exact hv'
    have key := e.τ₀_u₀ x v hv hv''
    have hsub : (⟨_, hv'⟩ : ↥(Q'.N₀ x)) = ⟨v, hv''⟩ := Subtype.ext h1
    rw [hsub]; exact key
  τ₁_u₁ x v hv hv' := by
    have h1 : ((scalarGL (1 : Kˣ) * (1 : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
      rw [scalarGL_one, one_mul, inv_one, Units.val_one, Matrix.one_mulVec]
    have hv'' : v ∈ Q'.N₁ x := by rw [← h1]; exact hv'
    have key := e.τ₁_u₁ x v hv hv''
    have hsub : (⟨_, hv'⟩ : ↥(Q'.N₁ x)) = ⟨v, hv''⟩ := Subtype.ext h1
    rw [hsub]; exact key

end Translate

end DrinfeldDatum
end FormalOmega
end CerednikDrinfeld

end
