/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.v1.Atlas.EllipticCurves.code.FiniteFields.Part5
import Lemma.Complex.Atlas.v1.EllipticCurves.code.FiniteFields
import Mathlib.FieldTheory.Finite.Extension
import Structure.v1.Atlas.EllipticCurves.code.FiniteFieldArith


namespace FiniteFieldArith

variable (intMulCost : ℕ → ℕ)

namespace Polynomial

section SqfreeFactorization

variable {k : Type*} [Field k]

open Classical

/-- One iteration of Yun's algorithm: from state `(v, w)`, compute
`g = gcd(v, w − v')`, then advance to the new state `(v/g, (w − v')/g)`. -/
noncomputable def yunStep (st : YunState k) : k[X] × YunState k :=
  let diff := st.w - derivative st.v
  let g := EuclideanDomain.gcd st.v diff
  let v_new := st.v / g
  let w_new := diff / g
  (g, ⟨v_new, w_new⟩)

/-- Initialization of Yun's algorithm: from input `f`, divide out `u = gcd(f, f')`
to set `v_1 = f/u` and `w_1 = f'/u`. -/
noncomputable def yunInit (f : k[X]) : YunState k :=
  let u := EuclideanDomain.gcd f (derivative f)
  ⟨f / u, derivative f / u⟩

/-- Iterate Yun's algorithm for a bounded number of steps `n`, collecting the
factor sequence `g_1, g_2, …`. Stops early when the current `v_i` equals the
computed `g_i`. -/
noncomputable def yunIterate (st : YunState k) : ℕ → List (k[X]) × YunState k
  | 0 => ([], st)
  | n + 1 =>
    let (g, st') := yunStep st
    if st.v = g then ([g], st')
    else
      let (gs, st'') := yunIterate st' n
      (g :: gs, st'')

/-- Top-level Yun's algorithm (Algorithm 3.46): start from `f`, initialize, and
iterate for at most `fuel` steps, returning the list of squarefree factors
`g_1, g_2, …, g_m`. -/
noncomputable def yunAlgorithm (f : k[X]) (fuel : ℕ) : List (k[X]) :=
  (yunIterate (yunInit f) fuel).1

/-- The polynomial `X^{q^j} - X` over a finite field `k` of cardinality `q`.
Its roots are exactly the elements of the unique subfield `𝔽_{q^j} ⊆ k̄`, so its
factorization isolates irreducibles of degree dividing `j`. Used in
Algorithm 3.47 / Algorithm 3.46 for distinct-degree factorization. -/
noncomputable def xPowCardPowSubX (k : Type*) [Field k] [Fintype k] (j : ℕ) : k[X] :=
  X ^ (Fintype.card k) ^ j - X

/-- One step of distinct-degree factorization: from `f`, compute
`g = gcd(f, X^{q^j} − X)` (the product of degree-`j` irreducible factors of `f`)
and the new remaining polynomial `f / g`. -/
noncomputable def distinctDegreeStep (f : k[X]) (j : ℕ) : k[X] × k[X] :=
  let g := EuclideanDomain.gcd f (xPowCardPowSubX k j)
  (g, f / g)

end SqfreeFactorization
end Polynomial
end FiniteFieldArith
