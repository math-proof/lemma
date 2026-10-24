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

open Polynomial Finset

namespace BerlekampRabin

section Defs

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Two nonzero elements `α`, `β` of a finite field `F` are of *different type* if
their `(q-1)/2`-th powers differ, where `q = |F|`. By Euler's criterion this means
exactly one of `α, β` is a quadratic residue. -/
def DifferentType (α β : F) : Prop :=
  α ≠ 0 ∧ β ≠ 0 ∧ α ^ (Fintype.card F / 2) ≠ β ^ (Fintype.card F / 2)

/-- Decidability of `DifferentType` (since equality in a finite field with decidable
equality is decidable). -/
noncomputable instance differentTypeDecidable (α β : F) :
    Decidable (DifferentType F α β) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The set of shifts `δ ∈ F` such that `α + δ` and `β + δ` are of different type
(in the sense of `DifferentType`). Used in Rabin's root-finding algorithm
(Algorithm 3.45 / Theorem 3.44). -/
noncomputable def differentTypeSet (α β : F) : Finset F :=
  Finset.univ.filter fun δ => DifferentType F (α + δ) (β + δ)

end Defs

section Bijection

variable {F : Type*} [Field F]

/-- The map `δ ↦ (α + δ)/(β + δ)`, used to put the different-type set in bijection
with the set of `γ` whose `(q-1)/2`-th power is `-1`. -/
noncomputable def phi (α β δ : F) : F := (α + δ) / (β + δ)

/-- Inverse of `phi`: given `γ`, the unique `δ` with `phi α β δ = γ` (when `α ≠ β`
and `γ ≠ 1`). -/
noncomputable def psi (α β γ : F) : F := (γ * β - α) / (1 - γ)

/-- Step 4b of Algorithm 3.45: compute `gcd(g, (X + δ)^((q-1)/2) - 1)`, a candidate
nontrivial factor of `g`. -/
noncomputable def berlekampRabinStep (g : F[X]) (δ : F) : F[X] :=
  EuclideanDomain.gcd g ((X + C δ) ^ (Fintype.card F / 2) - 1)

/-- Step 2 of Algorithm 3.45: compute `gcd(f, X^q - X)`, the product of `(X - α)` over
all roots `α ∈ F_q` of `f`. -/
noncomputable def berlekampRabinInit (f : F[X]) : F[X] :=
  EuclideanDomain.gcd f (X ^ Fintype.card F - X)

/-- Read off the unique root from a monic linear polynomial `g = X - r`:
`extractRoot g = -coeff 0 / leadingCoeff`. -/
noncomputable def extractRoot (g : F[X]) : F :=
  -g.coeff 0 / g.leadingCoeff

/-- Step 4c of Algorithm 3.45: replace `g` by whichever of `h` or `g/h` has lower
degree, provided `h` is a nontrivial proper factor. -/
noncomputable def chooseFactor (g h : F[X]) : F[X] :=
  if 0 < h.natDegree ∧ h.natDegree < g.natDegree then
    if h.natDegree ≤ g.natDegree - h.natDegree then h
    else g / h
  else g

/-- A single iteration of the inner loop in Algorithm 3.45: run `berlekampRabinStep`
with shift `δ`, then `chooseFactor`. -/
noncomputable def berlekampRabinIteration (g : F[X]) (δ : F) : F[X] :=
  let h := berlekampRabinStep F g δ
  chooseFactor F g h

/-- The inner while-loop of Algorithm 3.45: iterate `berlekampRabinIteration` over a
supplied list of random shifts `δ`, stopping early once `deg g ≤ 1`. -/
noncomputable def berlekampRabinLoop : F[X] → List F → F[X]
  | g, [] => g
  | g, δ :: rest =>
    if g.natDegree ≤ 1 then g
    else berlekampRabinLoop (berlekampRabinIteration F g δ) rest

/-- Algorithm 3.45 (Rabin 1980): given a monic polynomial `f ∈ F_q[X]`, return some
root of `f` in `F_q` if one exists. Returns `0` if `f(0) = 0`; otherwise reduces to
the squarefree part `g = gcd(f, X^q - X)` containing exactly the roots, and iteratively
splits `g` using random shifts. -/
noncomputable def berlekampRabinAlgorithm (f : F[X]) (deltas : List F) : Option F :=

  if f.IsRoot 0 then some 0
  else

    let g := berlekampRabinInit F f

    if g.natDegree = 0 then none
    else

      let g' := berlekampRabinLoop F g deltas

      some (extractRoot F g')

set_option linter.unusedSectionVars false in

/-- Inner loop of Yun's squarefree factorization (Algorithm 3.46): given `v, w` and a
fuel bound, repeatedly compute `g_i = gcd(v_i, w_i - v_i')` and refresh
`v_{i+1} = v_i / g_i`, `w_{i+1} = (w_i - v_i') / g_i`. -/
noncomputable def yunLoop : F[X] → F[X] → ℕ → List (F[X])
  | v, _w, 0 => [v]
  | v, w, fuel + 1 =>
    let g := EuclideanDomain.gcd v (w - Polynomial.derivative v)
    if v = g then [g]
    else
      let v' := v / g
      let w' := (w - Polynomial.derivative v) / g
      g :: yunLoop v' w' fuel

/-- Algorithm 3.46 (Yun): squarefree factorization of `f ∈ F_q[X]` (in characteristic
not dividing `deg f`). Returns a list `[g_1, …, g_m]` of squarefree pairwise coprime
polynomials with `f = g_1 · g_2^2 · ⋯ · g_m^m`. -/
noncomputable def yunSquarefreeFactor (f : F[X]) : List (F[X]) :=
  let u := EuclideanDomain.gcd f (Polynomial.derivative f)
  let v₁ := f / u
  let w₁ := Polynomial.derivative f / u
  yunLoop F v₁ w₁ f.natDegree

/-- Reconstruct `f` from its squarefree factorization `[g_1, …, g_m]` as the product
`∏_i g_i^i` (with 1-based indexing). -/
noncomputable def sqfreeProduct (factors : List (F[X])) : F[X] :=
  (factors.zipIdx 1 |>.map (fun ⟨g, i⟩ => g ^ i)).prod

/-- The correctness predicate for a squarefree factorization (output of
Algorithm 3.46): the list is nonempty, recovers `f` as `∏ g_i^i`, each `g_i` is
squarefree, the factors are pairwise coprime, and the last factor is not `1`. -/
structure IsSquarefreeFactorization (f : F[X]) (factors : List (F[X])) : Prop where
  nonempty : factors ≠ []
  prod_eq : f = sqfreeProduct F factors
  sqfree : ∀ g ∈ factors, Squarefree g
  coprime : factors.Pairwise (fun g h => IsCoprime g h)
  last_ne_one : factors.getLast nonempty ≠ 1

end YunAlgorithm

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

/-- Correctness predicate for the output of `cantorZassenhausAlgorithm`: the indexed
family `factors : Fin n → F[X]` consists of irreducibles, `f = ∏ (factors i)^(mult i)`,
multiplicities are positive, and distinct indices give non-associated factors. -/
structure IsIrreducibleFactorization (f : F[X]) (n : ℕ)
    (factors : Fin n → F[X]) (multiplicities : Fin n → ℕ) : Prop where
  irred : ∀ i : Fin n, Irreducible (factors i)
  prod_eq : f = ∏ i : Fin n, (factors i) ^ (multiplicities i)
  mult_pos : ∀ i : Fin n, 0 < multiplicities i
  pairwise : ∀ i j : Fin n, i ≠ j → ¬ Associated (factors i) (factors j)
