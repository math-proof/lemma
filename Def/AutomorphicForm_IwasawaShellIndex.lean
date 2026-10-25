import Lemma.NumberField.AdelicLevel
import Def.AutomorphicForm_AdelicLsXi
import Def.AutomorphicForm_ConstantTerm

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

noncomputable section

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K]

def finEntryValuation (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    WithZero (Multiplicative ℤ) :=
  Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v)

def finDetValuation (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) : WithZero (Multiplicative ℤ) :=
  Valued.v (((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v)

def iwasawaShellIndex (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) : ℤ :=
  2 * WithZero.log (max (finEntryValuation K v g 1 0) (finEntryValuation K v g 1 1)) -
    WithZero.log (finDetValuation K v g)

variable {K}

section Lemmas

variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

def adeleEvalFin : AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  (finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)


def localMatrix : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) :=
  (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).map (adeleEvalFin v)

end Lemmas

end AutomorphicForm

end
