import Mathlib
import Structure.CerednikDrinfeld_SpecialFormalModule
import Def.CerednikDrinfeld_ModuliPackageDescent

set_option autoImplicit false

namespace CerednikDrinfeld

namespace SpecialFormal

namespace ModuliPackage

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

structure Hom (G H : ModuliPackage.{0, 0} p O) where

  app : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), G.obj B ψ hB → H.obj B ψ hB

  naturality : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (x : G.obj B ψ hB), app B' ψ' hB' (G.map hB hB' f hf x) = H.map hB hB' f hf (app B ψ hB x)

end ModuliPackage

end SpecialFormal

end CerednikDrinfeld
