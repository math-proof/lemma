import Def.HeckeCharacter_FiniteOrder
import Lemma.Matrix.AdelicLevel
import Def.AutomorphicForm_ConstantTerm
import Instance.AutomorphicForm_GaussTwist
import Abbrev.AutomorphicForm_GaussTwist

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Matrix.AdelicLevel Matrix

namespace Ideal.GaussTwist

section LocalRing

variable (A : Type*) [CommRing A] [IsLocalRing A]

def unitQuotLift (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) : Aˣ :=
  Function.surjInv (units_map_quotient_maximalIdeal_pow_surjective A n) x

end LocalRing

section Local

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

def localUnif : v.adicCompletion K := ((v.valuation_exists_uniformizer K).choose : K)

end Local

section Adelic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def adeleOn (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) : FiniteAdeleRing R K :=
  ⟨fun w => if w ∈ S then y w else 0,
    S.eventually_cofinite_notMem.mono fun w hw => by
      dsimp only
      rw [if_neg hw]
      exact (w.adicCompletionIntegers K).zero_mem⟩

def finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j =>
    (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, m i j) : AdeleRing R K)

def finLift (g : GL (Fin 2) (FiniteAdeleRing R K)) : GL (Fin 2) (AdeleRing R K) where
  val := finPair (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  inv := finPair
    ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  val_inv := by rw [finPair_mul, Units.mul_inv, finPair_one]
  inv_val := by rw [finPair_mul, Units.inv_mul, finPair_one]

end Adelic

section Gauss

variable (F : Type) [Field F] [NumberField F]

open scoped Classical

def modulusPrimes (𝔣 : Ideal (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 F)) :=
  if h : 𝔣 = ⊥ then ∅ else (Ideal.finite_factors (fun h' => h h')).toFinset

def GaussIndex (𝔣 : Ideal (𝓞 F)) : Type :=
  ∀ 𝔭 : modulusPrimes F 𝔣, LocalGaussFactor F 𝔣 𝔭.1

noncomputable def gaussRep (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣)
    (𝔭 : modulusPrimes F 𝔣) : (𝔭.1.adicCompletionIntegers F)ˣ :=
  unitQuotLift (𝔭.1.adicCompletionIntegers F)
    (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣) (u 𝔭)

noncomputable def gaussUnif (𝔭 : HeightOneSpectrum (𝓞 F)) : 𝔭.adicCompletion F :=
  localUnif F 𝔭

noncomputable def gaussY (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣)
    (𝔭 : HeightOneSpectrum (𝓞 F)) : 𝔭.adicCompletion F :=
  if h : 𝔭 ∈ modulusPrimes F 𝔣 then
    ((gaussRep F 𝔣 u ⟨𝔭, h⟩ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
      * (gaussUnif F 𝔭)⁻¹ ^ (HeckeCharacter.idealMultiplicity F 𝔭 𝔣)
  else 0

def unitIdele (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (∏ 𝔭 : modulusPrimes F 𝔣, localUnit (𝓞 F) F 𝔭.1
    ⟨(r 𝔭 : 𝔭.1.adicCompletionIntegers F), (r 𝔭)⁻¹, by simp, by simp⟩)

def gaussUnitIdele (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (∏ 𝔭 : modulusPrimes F 𝔣, localUnit (𝓞 F) F 𝔭.1
    ⟨(gaussRep F 𝔣 u 𝔭 : 𝔭.1.adicCompletionIntegers F),
     (gaussRep F 𝔣 u 𝔭)⁻¹, by simp, by simp⟩)

def gaussWt (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) : ℂ :=
  ((η (gaussUnitIdele F 𝔣 u) : ℂˣ) : ℂ)

def gaussTrans (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) : AdelicGL2 (𝓞 F) F :=
  finLift (unipotentGL2 (adeleOn (modulusPrimes F 𝔣) (gaussY F 𝔣 u)))

def gaussSumFn (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => ∑ u : GaussIndex F 𝔣, gaussWt F η 𝔣 u * φ (g * gaussTrans F 𝔣 u)

end Gauss

end Ideal.GaussTwist

end
