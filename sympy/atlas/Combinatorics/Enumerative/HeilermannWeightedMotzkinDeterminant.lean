/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/HeilermannWeightedMotzkinDeterminant.lean -/

import sympy.atlas.NumberTheory.HankelTransform
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

section
open scoped BigOperators

-- Helpers for Heilermann's formula (production-matrix factorisation).
private noncomputable def motzkinE {K : Type*} [CommRing K] (alpha beta : ℕ → K) : ℕ → ℕ → K
  | 0 => fun k => if k = 0 then 1 else 0
  | (j + 1) => fun k =>
      motzkinE alpha beta j (k + 1) + alpha k * motzkinE alpha beta j k +
        (if k = 0 then 0 else beta k * motzkinE alpha beta j (k - 1))
end
end MetaMathlibExt
