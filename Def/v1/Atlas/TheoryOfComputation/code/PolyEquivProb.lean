/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part5
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Probabilistic
import Mathlib.Algebra.MvPolynomial.CommRing


namespace PolyEquivProb

open Finset MvPolynomial Fintype

/-- The probability that two multivariate polynomials `p₁, p₂ ∈ F[X_1, …, X_m]`
agree on a uniformly random point in `F^m`, defined as the number of points where
`eval r p₁ = eval r p₂` divided by `|F|^m`. -/
noncomputable def agreementProb
    {F : Type*} [CommRing F] [IsDomain F] [Fintype F] [DecidableEq F]
    {m : ℕ} (p₁ p₂ : MvPolynomial (Fin m) F) : ℚ≥0 :=
  ((Finset.univ.filter (fun r : Fin m → F =>
    MvPolynomial.eval r p₁ = MvPolynomial.eval r p₂)).card : ℚ≥0) /
    ((Fintype.card F : ℚ≥0) ^ m)

/-- Embeds a Boolean assignment `v : Fin m → Bool` into a field point
`Fin m → F` by sending `true ↦ 1` and `false ↦ 0`. -/
noncomputable def boolToField {m : ℕ} {F : Type*} [CommRing F]
    (v : Fin m → Bool) : Fin m → F :=
  fun i => if v i then 1 else 0

/-- The support of a Boolean vector `v : Fin m → Bool`, i.e. the set of indices
where `v i = true`. -/
def boolSupport {m : ℕ} (v : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => v i = true)

/-- The (unique) multilinear extension of a Boolean function `f : {0,1}^m → F` to
a multivariate polynomial over `F`. For each subset `S ⊆ Fin m` we form the
indicator polynomial `(∏_{i ∈ S} X_i) · (∏_{i ∉ S} (1 - X_i))`, weight it by
`f(1_S)`, and sum over all subsets. -/
noncomputable def multilinearExtension {m : ℕ} {F : Type*} [CommRing F]
    (f : (Fin m → Bool) → F) : MvPolynomial (Fin m) F :=
  ∑ S ∈ Finset.univ.powerset,
    MvPolynomial.C (f (fun i => decide (i ∈ S))) *
    (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin m) F)) *
    (∏ i ∈ Finset.univ \ S, ((1 : MvPolynomial (Fin m) F) - MvPolynomial.X i))

/-- Arithmetization of a (read-once) branching program: produce the multilinear
extension of its Boolean evaluation function, viewed as a polynomial over `F`. -/
noncomputable def arithmetize {m : ℕ} {F : Type*} [CommRing F]
    (bp : BranchingPrograms.BranchingProgram m) : MvPolynomial (Fin m) F :=
  multilinearExtension (fun v => if bp.eval v then 1 else 0)

end PolyEquivProb
