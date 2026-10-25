import Mathlib
import Instance.MvFormalGroup_NegV2
import Structure.CerednikDrinfeld_SpecialFormalModule
import Structure.CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld
namespace SpecialFormal

open FormalOmega

variable {p : ℕ} [Fact p.Prime]

namespace Rigidified

variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B : Type u} [CommRing B]


end Rigidified

namespace ModuliPackage

variable (𝒪 : Type) [CommRing 𝒪] {O : Type} [CommRing O] [Algebra 𝒪 O]

structure GPoint (M : ModuliPackage.{0, 0} p O) (B : Type) [CommRing B] [Algebra 𝒪 B] : Type where

  ψ : O →ₐ[𝒪] B

  nilp : IsNilpotent (p : B)

  pt : M.obj B (ψ : O →+* B) nilp

namespace GPoint

variable {𝒪}
variable {M : ModuliPackage.{0, 0} p O} {B : Type} [CommRing B] [Algebra 𝒪 B]


end GPoint


namespace G

variable {𝒪}
variable {M : ModuliPackage.{0, 0} p O} (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
  (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
  (Fr : O ≃ₐ[𝒪] O)


end G

end ModuliPackage

end SpecialFormal
end CerednikDrinfeld

end
