import Mathlib
import Lemma.Definitions.Def_MvFormalGroup_NegV2
import Lemma.Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Lemma.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Lemma.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

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

@[simp] theorem algHomOfComp_apply (c : 𝒪 →+* O) {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B)
    (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ') (b : B) :
    algHomOfComp c ψ ψ' f hf b = f b := rfl

theorem coe_algHomOfComp (c : 𝒪 →+* O) {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B)
    (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ') :
    (algHomOfComp c ψ ψ' f hf : B →+* B') = f := rfl

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

def omegaPackage {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {O : Type} [CommRing O]
    (p : ℕ) [Fact p.Prime] (π : 𝒪) (c : 𝒪 →+* O) :
    CerednikDrinfeld.SpecialFormal.ModuliPackage.{0, 0} p O :=
  (Omega K π).toModuliPackage p c

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
