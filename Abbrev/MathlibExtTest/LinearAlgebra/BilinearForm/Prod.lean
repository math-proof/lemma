/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/BilinearForm/Prod.lean -/


import Instance.LinearAlgebra.BilinearForm.Prod
import Lemma.Matrix.BilinearForm.Prod
import Mathlib.RingTheory.Localization.FractionRing
import Theorem.MathlibExtTest.LinearAlgebra.BilinearForm.Prod
open LinearMap (BilinForm)
open Module

/-!
# Tests for the orthogonal product of bilinear forms

Examples exercising `BilinForm.prod` and its nondegeneracy, perfectness,
and dual-submodule API, including a source-shaped Noetherian-domain
fraction-field case.
-/


namespace LinearMap

namespace BilinForm

section PerfPair

/-- A concrete perfect pairing from the canonical dual equivalence. -/
noncomputable abbrev testPair : BilinForm ℚ (Fin 1 → ℚ) :=
  (Module.Free.chooseBasis ℚ (Fin 1 → ℚ)).toDualEquiv.toLinearMap

end PerfPair
end BilinForm
end LinearMap
