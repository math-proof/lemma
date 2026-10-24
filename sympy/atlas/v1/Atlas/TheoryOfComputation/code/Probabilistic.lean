/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.Roots
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.BPP
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Nat.Prime.Infinite

import Mathlib.Algebra.Order.Archimedean.Basic

namespace Probabilistic

/-- A formal description of a pair of finite simple graphs `(G, H)`, packaged
together with the decidability and finiteness instances needed to manipulate
them constructively. Used as the underlying mathematical object for the graph
isomorphism problem `ISO`. -/
structure GraphPairDesc where
  V : Type
  instFintypeV : Fintype V
  instDecEqV : DecidableEq V
  G : SimpleGraph V
  instDecRelG : DecidableRel G.Adj
  W : Type
  instFintypeW : Fintype W
  instDecEqW : DecidableEq W
  H : SimpleGraph W
  instDecRelH : DecidableRel H.Adj

/-- A graph-pair description `d` is *isomorphic* if there exists a graph
isomorphism `d.G ≃g d.H`. This is the property defining membership in `ISO`. -/
def GraphPairDesc.isIsomorphic (d : GraphPairDesc) : Prop :=
  Nonempty (d.G ≃g d.H)

/-- A faithful encoding of graph-pair descriptions as strings over alphabet `Γ`,
specified by an injective `encode` function and a `decode` function that inverts
it. Used to turn the mathematical object `GraphPairDesc` into the language
`ISO ⊆ List Γ`. -/
structure GraphPairEncoding (Γ : Type) where
  encode : GraphPairDesc → List Γ
  decode : List Γ → Option GraphPairDesc
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The graph isomorphism language

`ISO = {⟨G, H⟩ ∣ G and H are isomorphic graphs}`,

defined here as the set of strings `s` over alphabet `Γ` that encode some
graph-pair description `d` for which `d.G ≃g d.H`. -/
def ISO {Γ : Type} (enc : GraphPairEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : GraphPairDesc, enc.encode d = s ∧ d.isIsomorphic}

/-- A language `A ⊆ Σ*` is *in BPP with error `ε`* if some polynomial-time
probabilistic Turing machine `M` decides `A` with two-sided error `ε`: there
exist `Q`, `M`, an exponent `k`, and a runtime bound `t'` such that `M` runs in
time `t'`, `t' = O(nᵏ)`, and `M.decidesWithError A ε t'` holds. The class BPP
itself corresponds to `ε = 1/3`. -/
def InBPPWithError {Γ : Type} [DecidableEq Γ] (ε : ℚ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : PTM Q Γ) (k : ℕ) (t' : ℕ → ℕ),
    M.runsInTime t' ∧
    IsBigO t' (fun n => n ^ k) ∧
    M.decidesWithError A ε t'

/-- The sequence of error bounds obtained by iterating the majority-vote
update: `iterError ε₁ 0 = ε₁`, and `iterError ε₁ (n+1) = e² (3 - 2e)` where
`e = iterError ε₁ n`. Each step corresponds to amplifying the BPP machine by a
three-fold majority vote. -/
noncomputable def iterError (ε₁ : ℚ) : ℕ → ℚ
  | 0 => ε₁
  | n + 1 => let e := iterError ε₁ n; e ^ 2 * (3 - 2 * e)

/-- A node of a branching program with `m` input variables and `N` total nodes.
A node is either a `query` on variable `var : Fin m` with two successors `zero,
one : Fin N` (followed depending on whether the bit is `0` or `1`), or an
`output` leaf carrying a Boolean answer. -/
inductive BPNode (m : ℕ) (N : ℕ) where
  | query (var : Fin m) (zero : Fin N) (one : Fin N) : BPNode m N
  | output (val : Bool) : BPNode m N

/-- A branching program on `m` Boolean input variables. It has `numNodes`
nodes (with node `0` being the start node) and a `nodes` table assigning each
index a `BPNode`. -/
structure BranchingProgram (m : ℕ) where
  numNodes : ℕ
  numNodes_pos : 0 < numNodes
  nodes : Fin numNodes → BPNode m numNodes

/-- Evaluate a branching program `bp` on a Boolean `assignment`. Execution
starts at node `0` and follows `query` edges according to the assignment; the
recursion is bounded by `bp.numNodes` units of fuel via the inner `go`. -/
def BranchingProgram.eval (bp : BranchingProgram m) (assignment : Fin m → Bool)
    : Bool :=
  go bp assignment ⟨0, bp.numNodes_pos⟩ bp.numNodes
where
  go (bp : BranchingProgram m) (assignment : Fin m → Bool)
      (node : Fin bp.numNodes) : ℕ → Bool
    | 0 => false
    | fuel + 1 =>
      match bp.nodes node with
      | BPNode.output val => val
      | BPNode.query var zero one =>
        if assignment var then go bp assignment one fuel
        else go bp assignment zero fuel

/-- Two branching programs are *equivalent* (`B₁ ≡ B₂`) if they compute the
same Boolean function: `bp₁.eval a = bp₂.eval a` for every assignment `a`. -/
def BPEquiv (bp₁ bp₂ : BranchingProgram m) : Prop :=
  ∀ assignment : Fin m → Bool, bp₁.eval assignment = bp₂.eval assignment

/-- A branching program is *read-once* if, along any computation path, each
input variable is queried at most once. Formally: for every list of nodes
`path` along which the program might step, any two indices `i, j` whose nodes
both `query` the same variable `v` must coincide. -/
def BranchingProgram.isReadOnce (bp : BranchingProgram m) : Prop :=
  ∀ (path : List (Fin bp.numNodes)),
    (∀ (i j : Fin path.length) (v : Fin m),
      (∃ z o, bp.nodes (path.get i) = BPNode.query v z o) →
      (∃ z o, bp.nodes (path.get j) = BPNode.query v z o) →
      i = j)

/-- A description of a pair `(B₁, B₂)` of read-once branching programs on the
same number of variables, together with proofs that each is read-once. This is
the mathematical object whose equivalence problem is `EQ_ROBP`. -/
structure ROBPPairDesc where
  numVars : ℕ
  B₁ : BranchingProgram numVars
  B₂ : BranchingProgram numVars
  B₁_readOnce : B₁.isReadOnce
  B₂_readOnce : B₂.isReadOnce

/-- The semantic equivalence relation on `ROBPPairDesc`: `d.B₁ ≡ d.B₂` as
Boolean functions. -/
def ROBPPairDesc.isEquivalent (d : ROBPPairDesc) : Prop :=
  BPEquiv d.B₁ d.B₂

/-- A faithful encoding of `ROBPPairDesc` as strings over alphabet `Γ`, used
to turn the abstract equivalence problem into a language `EQ_ROBP ⊆ List Γ`. -/
structure ROBPPairEncoding (Γ : Type) where
  encode : ROBPPairDesc → List Γ
  decode : List Γ → Option ROBPPairDesc
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The language of equivalent read-once branching programs:

`EQ_ROBP = {⟨B₁, B₂⟩ ∣ B₁ ≡ B₂ as ROBPs}`,

with the pair encoded as a string over `Γ` using `enc`. Membership in BPP is
proved in `EQ_ROBP_in_BPP`. -/
def EQ_ROBP {Γ : Type} (enc : ROBPPairEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : ROBPPairDesc, enc.encode d = s ∧ d.isEquivalent}

/-- Number of random bits used by the `EQ_ROBP` BPP decider on inputs of
length `n`: a polynomial budget of `n² + 1` bits, enough to sample a random
field element per variable. -/
def eqROBP_numBits (n : ℕ) : ℕ := n ^ 2 + 1

/-- **Soundness bound for the `EQ_ROBP` randomized decider.** On a no-instance
`(B₁, B₂)` (with `B₁ ≢ B₂`), the probability that the verifier accepts is at
most `1/3`. This is the Schwartz-Zippel-based bound from Sipser Lecture 24:
when the arithmetizations `p₁, p₂` (each of total degree `≤ numVars` in every
variable) disagree, `Pr[p₁(r) = p₂(r)] ≤ d·m/q ≤ 1/3` for `q ≥ 3·numVars`. -/
noncomputable def edgeFactor {m : ℕ} (R : Type*) [CommRing R] (i : Fin m) (b : Bool) :
    MvPolynomial (Fin m) R :=
  if b then X i else 1 - X i

open MvPolynomial Finset in
/-- The monomial associated to a Boolean assignment `a : Fin m → Bool`:
`∏ᵢ edgeFactor R i (a i)`, i.e. the product `∏ᵢ Xᵢ^{aᵢ} (1 - Xᵢ)^{1 - aᵢ}`.
Over a Boolean point `x`, this is the indicator `[x = a]`. -/
noncomputable def pathMonomial {m : ℕ} (R : Type*) [CommRing R] (a : Fin m → Bool) :
    MvPolynomial (Fin m) R :=
  ∏ i : Fin m, edgeFactor R i (a i)

open MvPolynomial Finset in
/-- Arithmetization of a Boolean function `f : 2^m → 2` as a multilinear
polynomial: sum of `pathMonomial R a` over all assignments `a` with `f a =
true`. On Boolean inputs this evaluates to `1` iff `f a = true`. -/
noncomputable def arithmetizeFn {m : ℕ} (R : Type*) [CommRing R]
    (f : (Fin m → Bool) → Bool) : MvPolynomial (Fin m) R :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = true), pathMonomial R a

open MvPolynomial Finset in
/-- Arithmetization of a branching program `bp`: the multivariate polynomial
representing the Boolean function `bp.eval`. Two equivalent ROBPs arithmetize
to equal polynomials, which is the algebraic core of the `EQ_ROBP ∈ BPP`
proof. -/
noncomputable def arithmetize {m : ℕ} (R : Type*) [CommRing R]
    (bp : BranchingProgram m) : MvPolynomial (Fin m) R :=
  arithmetizeFn R bp.eval
