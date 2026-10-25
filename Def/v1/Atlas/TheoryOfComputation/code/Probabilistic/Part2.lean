/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.Roots
import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.Archimedean.Basic
import Structure.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part2


namespace Probabilistic

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

end Probabilistic
