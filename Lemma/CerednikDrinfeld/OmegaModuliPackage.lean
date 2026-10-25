import Mathlib
import Lemma.MvFormalGroup.NegV2
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Def.CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Lemma.CerednikDrinfeld.FormalUpperHalfPlaneFunctor
import Def.CerednikDrinfeld_OmegaModuliPackage

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

namespace FormalOmega

namespace AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O]


@[simp] theorem algHomOfComp_apply (c : 𝒪 →+* O) {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B)
    (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ') (b : B) :
    algHomOfComp c ψ ψ' f hf b = f b := rfl

theorem coe_algHomOfComp (c : 𝒪 →+* O) {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B)
    (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ') :
    (algHomOfComp c ψ ψ' f hf : B →+* B') = f := rfl


@[simp] theorem toModuliPackage_obj (p : ℕ) [Fact p.Prime] (F : AlgFunctor 𝒪) (c : 𝒪 →+* O)
    (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) :
    (F.toModuliPackage p c).obj B ψ hB = @AlgFunctor.obj 𝒪 _ F B _ (ψ.comp c).toAlgebra := rfl

theorem toModuliPackage_map (p : ℕ) [Fact p.Prime] (F : AlgFunctor 𝒪) (c : 𝒪 →+* O)
    {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (x : (F.toModuliPackage p c).obj B ψ hB) :
    (F.toModuliPackage p c).map hB hB' f hf x =
      @AlgFunctor.map 𝒪 _ F B _ (ψ.comp c).toAlgebra B' _ (ψ'.comp c).toAlgebra (algHomOfComp c ψ ψ' f hf) x := rfl

end AlgFunctor


theorem omegaPackage_obj {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {O : Type} [CommRing O]
    (p : ℕ) [Fact p.Prime] (π : 𝒪) (c : 𝒪 →+* O) (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) :
    (omegaPackage (K := K) p π c).obj B ψ hB = @OmegaObj 𝒪 _ K _ _ π B _ (ψ.comp c).toAlgebra := rfl

theorem omegaPackage_map {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {O : Type} [CommRing O]
    (p : ℕ) [Fact p.Prime] (π : 𝒪) (c : 𝒪 →+* O)
    {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (d : (omegaPackage (K := K) p π c).obj B ψ hB) :
    (omegaPackage (K := K) p π c).map hB hB' f hf d =
      @DeligneDatum.map 𝒪 _ K _ _ π B _ (ψ.comp c).toAlgebra B' _ (ψ'.comp c).toAlgebra
        (AlgFunctor.algHomOfComp c ψ ψ' f hf) d := rfl

end FormalOmega

end CerednikDrinfeld

end
