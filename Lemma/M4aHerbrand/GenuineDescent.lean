import Def.M4aHerbrand_IdeleClassVocab
import Def.M4aHerbrand_AdeleBaseChange
import Lemma.M4aHerbrand.GenuineTensorEquiv
import Instance.M4aHerbrand_AdeleTopologyFacts

set_option autoImplicit false

noncomputable section

namespace M4aHerbrand.GenuineDescent

open NumberField TensorProduct IsDedekindDomain M4aHerbrand M4aHerbrand.Bridge

section AnyProducer

variable {A K B' L : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [NumberField K] [Algebra A K]
  [IsFractionRing A K] [Module.Free ℤ A] [Module.Finite ℤ A]
  [CommRing B'] [IsDedekindDomain B'] [Field L] [NumberField L] [Algebra B' L] [IsFractionRing B' L]
  [Module.Free ℤ B'] [Module.Finite ℤ B'] [Algebra K L]

theorem hcont_of_continuous_β (B : AdeleBaseChange A K B' L) (hβ : Continuous B.β) :
    ∀ σ : L ≃ₐ[K] L, letI := B.β.toAlgebra; Continuous (actOf A K B' L B.tensorEquiv σ) := by
  letI := B.β.toAlgebra
  intro σ
  exact continuous_conjAct_of_continuous_of_free A K B' L hβ B.tensorEquiv σ

def descentOfContinuousβ (B : AdeleBaseChange A K B' L) (hβ : Continuous B.β) : IdeleGaloisDescent B' K L :=
  B.toIdeleGaloisDescent (hcont_of_continuous_β B hβ)

theorem descentOfContinuousβ_act (B : AdeleBaseChange A K B' L) (hβ : Continuous B.β) (g : L ≃ₐ[K] L) :
    (descentOfContinuousβ B hβ).act g = letI := B.β.toAlgebra; actOf A K B' L B.tensorEquiv g := rfl

omit [NumberField K] [Module.Free ℤ A] [Module.Finite ℤ A] [NumberField L] [Module.Free ℤ B'] [Module.Finite ℤ B'] in

theorem continuous_β_of_prodMap (B : AdeleBaseChange A K B' L)
    (βi : InfiniteAdeleRing K →+* InfiniteAdeleRing L) (βf : FiniteAdeleRing A K →+* FiniteAdeleRing B' L)
    (h : B.β = RingHom.prodMap βi βf) (hinf : Continuous βi) (hfin : Continuous βf) : Continuous B.β := by
  rw [h]; exact Continuous.prodMap hinf hfin

end AnyProducer
section RingOfIntegers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def genuineDescent (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (hβ : Continuous B.β) : IdeleGaloisDescent (𝓞 L) K L :=
  descentOfContinuousβ B hβ

end RingOfIntegers

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def bgenOfTensorEquiv
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) :
    AdeleBaseChange (𝓞 K) K (𝓞 L) L where
  β := genuineβ K L
  β_compat := genuineβ_compat K L
  tensorEquiv := te
  tensorEquiv_one_tmul := hte

def genuineDescentOfTensorEquiv
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) :
    IdeleGaloisDescent (𝓞 L) K L :=
  genuineDescent (bgenOfTensorEquiv K L te hte) (continuous_genuineβ K L)

theorem genuineDescentOfTensorEquiv_act
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) (g : L ≃ₐ[K] L) :
    (genuineDescentOfTensorEquiv K L te hte).act g =
      letI := (genuineβ K L).toAlgebra; actOf (𝓞 K) K (𝓞 L) L te g := rfl

end Genuine

section Construction

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def genuineBaseChange : AdeleBaseChange (𝓞 K) K (𝓞 L) L :=
  bgenOfTensorEquiv K L (genuineTensorEquiv K L) (genuineTensorEquiv_one_tmul K L)

theorem genuineBaseChange_β : (genuineBaseChange K L).β = genuineβ K L := rfl

def genuineDescentDatum : IdeleGaloisDescent (𝓞 L) K L :=
  genuineDescentOfTensorEquiv K L (genuineTensorEquiv K L) (genuineTensorEquiv_one_tmul K L)

theorem genuineDescentDatum_act (g : L ≃ₐ[K] L) :
    (genuineDescentDatum K L).act g =
      letI := (genuineβ K L).toAlgebra; actOf (𝓞 K) K (𝓞 L) L (genuineTensorEquiv K L) g := rfl

end Construction

end M4aHerbrand.GenuineDescent

end
