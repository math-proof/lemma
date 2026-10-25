import Lemma.Matrix.SiegelReduction

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace NumberField

namespace AdelicHeight

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates
  AutomorphicForm.SiegelReduction NumberField.AdelicLevel NumberField.InfinitePlace

section Local

variable {K : Type*} [NormedField K]

def rowMaxNorm (M : Matrix (Fin 2) (Fin 2) K) : ℝ := max ‖M 1 0‖ ‖M 1 1‖


def finLocalHeight (g : GL (Fin 2) K) : ℝ :=
  ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2


end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

def finHeight (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), finLocalHeight (finComponent (𝓞 F) F v g)

def adelicHeight (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g)

variable {F}


end Adelic

end AdelicHeight

end NumberField
