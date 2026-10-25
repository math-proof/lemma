import Mathlib
import Instance.MvFormalGroup_NegV2
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Def.CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Lemma.CerednikDrinfeld.FormalUpperHalfPlaneFunctor

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

namespace FormalOmega

namespace AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O]

def algHomOfComp (c : 𝒪 →+* O) {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B')
    (f : B →+* B') (hf : f.comp ψ = ψ') :
    letI := (ψ.comp c).toAlgebra; letI := (ψ'.comp c).toAlgebra; B →ₐ[𝒪] B' :=
  letI := (ψ.comp c).toAlgebra; letI := (ψ'.comp c).toAlgebra
  { toRingHom := f
    commutes' := fun r => by
      show f (ψ (c r)) = ψ' (c r)
      rw [← hf]
      rfl }


def toModuliPackage (p : ℕ) [Fact p.Prime] (F : AlgFunctor 𝒪) (c : 𝒪 →+* O) :
    CerednikDrinfeld.SpecialFormal.ModuliPackage.{0, 0} p O where
  obj B _ ψ _ := @AlgFunctor.obj 𝒪 _ F B _ (ψ.comp c).toAlgebra
  map {B B'} _ _ {ψ ψ'} _ _ f hf x :=
    @AlgFunctor.map 𝒪 _ F B _ (ψ.comp c).toAlgebra B' _ (ψ'.comp c).toAlgebra (algHomOfComp c ψ ψ' f hf) x
  map_id {B} _ {ψ} _ x := by
    letI := (ψ.comp c).toAlgebra
    have h : algHomOfComp c ψ ψ (RingHom.id B) (RingHom.id_comp ψ) = AlgHom.id 𝒪 B := AlgHom.ext fun _ => rfl
    show F.map (algHomOfComp c ψ ψ (RingHom.id B) (RingHom.id_comp ψ)) x = x
    rw [h]
    exact F.map_id x
  map_comp {B B' B''} _ _ _ {ψ ψ' ψ''} _ _ _ g f hf hg x := by
    letI := (ψ.comp c).toAlgebra; letI := (ψ'.comp c).toAlgebra; letI := (ψ''.comp c).toAlgebra
    have h : algHomOfComp c ψ ψ'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) =
        (algHomOfComp c ψ' ψ'' g hg).comp (algHomOfComp c ψ ψ' f hf) := AlgHom.ext fun _ => rfl
    show F.map (algHomOfComp c ψ ψ'' (g.comp f) _) x =
      F.map (algHomOfComp c ψ' ψ'' g hg) (F.map (algHomOfComp c ψ ψ' f hf) x)
    rw [h]
    exact F.map_comp _ _ x

end AlgFunctor

def omegaPackage {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {O : Type} [CommRing O]
    (p : ℕ) [Fact p.Prime] (π : 𝒪) (c : 𝒪 →+* O) :
    CerednikDrinfeld.SpecialFormal.ModuliPackage.{0, 0} p O :=
  (Omega K π).toModuliPackage p c

end FormalOmega

end CerednikDrinfeld

end
