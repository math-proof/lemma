/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/HeilermannWeightedMotzkin.lean -/

module

public import Def.NumberTheory.HankelTransform
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

namespace MetaMathlibExt

section

noncomputable def motzkinH {K : Type*} [Ring K] (F : ℕ → PowerSeries K) :
    ℕ → PowerSeries K
  | 0 => F 0
  | (j + 1) => F (j + 1) * motzkinH F j * PowerSeries.X

noncomputable def motzkinM {K : Type*} [Ring K] (F : ℕ → PowerSeries K) :
    ℕ → ℕ → K :=
  fun n j => PowerSeries.coeff n (motzkinH F j)

end
end MetaMathlibExt
