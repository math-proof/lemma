import Lemma.Definitions.Def_AutomorphicForm_HeckeEigensystem
import Lemma.Definitions.Def_DedekindDomain_IntegralClosure

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm.SatakeCombination

open MvPolynomial in

def univWord (n k j : ℕ) : MvPolynomial (Fin 2) ℂ :=
  satakePow (n + 1) (X 0) (X 1) ^ k * ((X 1) ^ (n + 1)) ^ j

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))

def slotDeg (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  v.asIdeal.inertiaDeg' (ws v).1.asIdeal

def slotWord (v : HeightOneSpectrum (𝓞 K)) (kv jv : ℕ) : MvPolynomial (Fin 2) ℂ :=
  univWord (slotDeg K L ws v - 1) kv jv

def slotCoeff (v : HeightOneSpectrum (𝓞 K)) (kv jv : ℕ) (r : Fin 2 →₀ ℕ) : ℂ :=
  (slotWord K L ws v kv jv).coeff r * (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) /
    (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ jv

variable (k j : HeightOneSpectrum (𝓞 K) → ℕ)

def slotIndex [DecidableEq (HeightOneSpectrum (𝓞 K))] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset ((v : HeightOneSpectrum (𝓞 K)) → v ∈ T → (Fin 2 →₀ ℕ)) :=
  T.pi fun v => (slotWord K L ws v (k v) (j v)).support

def slotFamilyCoeff (T : Finset (HeightOneSpectrum (𝓞 K)))
    (m : (v : HeightOneSpectrum (𝓞 K)) → v ∈ T → (Fin 2 →₀ ℕ)) : ℂ :=
  ∏ v ∈ T.attach, slotCoeff K L ws v.1 (k v.1) (j v.1) (m v.1 v.2)

end AutomorphicForm.SatakeCombination

example : (AutomorphicForm.SatakeCombination.univWord 0 1 0).coeff (Finsupp.single 0 1) = 1 := by
  simp [AutomorphicForm.SatakeCombination.univWord, AutomorphicForm.satakePow, MvPolynomial.coeff_X']

example : (AutomorphicForm.SatakeCombination.univWord 0 0 1).coeff (Finsupp.single 1 1) = 1 := by
  simp [AutomorphicForm.SatakeCombination.univWord, AutomorphicForm.satakePow, MvPolynomial.coeff_X']

end
