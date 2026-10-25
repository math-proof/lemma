/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Structure.v1.Atlas.EllipticCurves.code.BerlekampRabin
open Polynomial Finset


namespace BerlekampRabin

section YunCorrectness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

set_option linter.unusedSectionVars false in

/-- One probabilistic splitting step in equal-degree (Cantor-Zassenhaus) factorization
(Step 3 of Algorithm 3.47): try `h₁ = gcd(g, u)`; if it is a proper factor, return it;
otherwise try `h₂ = gcd(g, u^((q^j - 1)/2) - 1)`; otherwise return `g`. -/
noncomputable def equalDegreeSplitStep (g u : F[X]) (j : ℕ) : F[X] :=
  let h₁ := EuclideanDomain.gcd g u
  if 0 < h₁.natDegree ∧ h₁.natDegree < g.natDegree then h₁
  else
    let s := (Fintype.card F ^ j - 1) / 2
    let h₂ := EuclideanDomain.gcd g (u ^ s - 1)
    if 0 < h₂.natDegree ∧ h₂.natDegree < g.natDegree then h₂
    else g

/-- The recursive splitting loop in equal-degree factorization (Step 3 of
Algorithm 3.47): given `g` of degree `> j`, repeatedly split using
`equalDegreeSplitStep` and recurse on both pieces, until each factor has degree `j`. -/
noncomputable def equalDegreeFactorLoop (j : ℕ) : F[X] → List (F[X]) → List (F[X])
  | g, [] => [g]
  | g, u :: rest =>
    if g.natDegree ≤ j then [g]
    else
      let h := equalDegreeSplitStep F g u j
      if 0 < h.natDegree ∧ h.natDegree < g.natDegree then
        equalDegreeFactorLoop j h rest ++ equalDegreeFactorLoop j (g / h) rest
      else
        equalDegreeFactorLoop j g rest

/-- Distinct-degree factorization step (Step 2 of Algorithm 3.47): compute
`g_j = gcd(g, X^(q^j) - X)`, the product of irreducible factors of `g` of degree `j`,
and return the pair `(g_j, g / g_j)`. -/
noncomputable def distinctDegreeStep (g : F[X]) (j : ℕ) : F[X] × F[X] :=
  let gj := EuclideanDomain.gcd g (X ^ (Fintype.card F ^ j) - X)
  (gj, g / gj)

/-- Cantor-Zassenhaus factorization of a squarefree polynomial `g` (Steps 2–3 of
Algorithm 3.47): iterate `distinctDegreeStep` for `j = 1, 2, …`, then split each
`g_j` further using `equalDegreeFactorLoop` if needed. -/
noncomputable def factorSquarefree (g : F[X]) (randomPolys : List (F[X])) : List (F[X]) :=
  let rec loop (remaining : F[X]) (j : ℕ) (fuel : ℕ) (acc : List (F[X])) : List (F[X]) :=
    if fuel = 0 ∨ remaining.natDegree = 0 then acc
    else
      let (gj, remaining') := distinctDegreeStep F remaining j
      let factors :=
        if gj.natDegree = 0 then []
        else if gj.natDegree = j then [gj]
        else equalDegreeFactorLoop F j gj randomPolys
      loop remaining' (j + 1) (fuel - 1) (acc ++ factors)
  loop g 1 g.natDegree []

/-- Algorithm 3.47 (Cantor-Zassenhaus): compute the complete irreducible factorization
of a monic `f ∈ F_q[X]` as a list of pairs `(p, i)`, where `p` is an irreducible
factor with multiplicity `i`. Uses Yun for the squarefree factorization and
`factorSquarefree` for each squarefree piece. -/
noncomputable def cantorZassenhausAlgorithm (f : F[X])
    (randomPolys : List (F[X])) : List (F[X] × ℕ) :=

  let sqfreeFactors := yunSquarefreeFactor F f


  (sqfreeFactors.zipIdx 1).flatMap fun ⟨gᵢ, i⟩ =>
    let irreds := factorSquarefree F gᵢ randomPolys
    irreds.map fun p => (p, i)

end YunCorrectness
end BerlekampRabin
