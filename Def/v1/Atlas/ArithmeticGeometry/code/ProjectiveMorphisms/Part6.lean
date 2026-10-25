/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Mathlib.Algebra.MvPolynomial.Monad
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part6


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveThm1518

open MvPolynomial

open scoped LinearAlgebra.Projectivization

open ProjectiveRegularFunction

open ProjectiveRatMap

variable {m n : ℕ} (k : Type*) [Field k]


/-- The homogeneous representative for the $i$-th coordinate function $x_i/x_0$ on $\mathbb{P}^n$. -/
noncomputable def coordHomogRep (n : ℕ) (k : Type*) [Field k] (i : Fin (n + 1)) :
    ProjectiveRegularFunction.HomogeneousRep n k where
  num := MvPolynomial.X i
  den := MvPolynomial.X 0
  deg := 1
  num_homog := MvPolynomial.isHomogeneous_X _ _
  den_homog := MvPolynomial.isHomogeneous_X _ _
  den_ne_zero := MvPolynomial.X_ne_zero _

/-- The projective rational function on $Y \subseteq \mathbb{P}^n$ given by the $i$-th coordinate $x_i/x_0$. -/
noncomputable def coordRatFun (n : ℕ) (k : Type*) [Field k]
    (Y : Set (ℙ k (Fin (n + 1) → k)))
    (i : Fin (n + 1)) :
    ProjectiveRatFun n k Y where
  reps := {r : ProjectiveRegularFunction.HomogeneousRep n k |
    r.equivOn k (coordHomogRep n k i) Y}
  reps_nonempty := ⟨coordHomogRep n k i,
    ProjectiveRegularFunction.HomogeneousRep.equivOn_refl k _ _⟩
  reps_equiv := fun r₁ hr₁ r₂ hr₂ => by
    exact ProjectiveRegularFunction.HomogeneousRep.equivOn_trans' r₁
      (coordHomogRep n k i) r₂ hr₁
      (ProjectiveRegularFunction.HomogeneousRep.equivOn_symm k
        r₂ (coordHomogRep n k i) Y hr₂)
  reps_maximal := fun r ⟨r₀, hr₀mem, hrequiv⟩ => by
    exact ProjectiveRegularFunction.HomogeneousRep.equivOn_trans' r r₀
      (coordHomogRep n k i) hrequiv hr₀mem

/-- The chosen homogeneous representative of $\theta(x_i/x_0) \in k(X)$ given a function-field homomorphism $\theta: k(Y) \to k(X)$. -/
noncomputable def inducedCoordRep
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (θ : ProjectiveFunctionFieldHom m n k X Y)
    (i : Fin (n + 1)) :
    ProjectiveRegularFunction.HomogeneousRep m k :=
  (θ.toFun (coordRatFun n k Y i)).reps_nonempty.choose

/-- The common degree shared by all the induced polynomials: the sum of the degrees of the coordinate representatives. Used to put all $\theta(x_i/x_0)$ on a common denominator. -/
noncomputable def inducedCommonDeg
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (θ : ProjectiveFunctionFieldHom m n k X Y) :
    ℕ :=
  ∑ j : Fin (n + 1), (inducedCoordRep k θ j).deg

/-- The $i$-th coordinate polynomial of the projective map induced by $\theta$: the $i$-th numerator times the product of all other denominators (clearing denominators to common degree). -/
noncomputable def inducedPoly
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (θ : ProjectiveFunctionFieldHom m n k X Y)
    (i : Fin (n + 1)) :
    MvPolynomial (Fin (m + 1)) k :=
  (inducedCoordRep k θ i).num *
    ∏ j ∈ Finset.univ.erase i, (inducedCoordRep k θ j).den

end ProjectiveThm1518
end
