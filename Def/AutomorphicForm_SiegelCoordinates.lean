import Def.AutomorphicForm_WindowedSiegelSet

open NumberField Matrix

noncomputable section

namespace AutomorphicForm

namespace SiegelCoordinates

open WindowedSiegel

section General

variable {K : Type*} [NormedField K]


def upperUnit (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, t]
    (by rw [Matrix.det_fin_two_of]; simp [ha, ht])

end General

section Complex

open ComplexConjugate

def xCoord (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (g 0 0 * conj (g 1 0) + g 0 1 * conj (g 1 1)) / (rowNormSq g : ℂ)

end Complex

end SiegelCoordinates

end AutomorphicForm

end
