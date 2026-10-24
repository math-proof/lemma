/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/HeilermannWeightedMotzkin.lean -/

import sympy.atlas.NumberTheory.HankelTransform
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Abel

namespace MetaMathlibExt

section

private noncomputable def motzkinH {K : Type*} [Ring K] (F : ℕ → PowerSeries K) :
    ℕ → PowerSeries K
  | 0 => F 0
  | (j + 1) => F (j + 1) * motzkinH F j * PowerSeries.X

private noncomputable def motzkinM {K : Type*} [Ring K] (F : ℕ → PowerSeries K) :
    ℕ → ℕ → K :=
  fun n j => PowerSeries.coeff n (motzkinH F j)
end
end MetaMathlibExt
