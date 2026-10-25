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
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part5


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- The image of a projective rational map $\varphi: X \dashrightarrow Y$: points $Q \in Y$ that arise as $\varphi(P)$ for some $P$ in the regular domain. -/
def ProjectiveRationalMap.image
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  {Q ∈ Y | ∃ P ∈ X, ∃ rep ∈ φ.reps,
    rep.isDefinedAt k P ∧
    ∀ i j, rep.evalVec k P i * Q.rep j = rep.evalVec k P j * Q.rep i}


/-- $S$ is Zariski-dense in $Y$ iff any polynomial vanishing on $S$ also vanishes on $Y$ (i.e., $S$'s Zariski closure contains $Y$). -/
def IsZariskiDenseIn {n : ℕ} (k : Type*) [Field k]
    (S Y : Set (ℙ k (Fin (n + 1) → k))) : Prop :=
  ∀ f : MvPolynomial (Fin (n + 1)) k,
    (∀ Q ∈ S, MvPolynomial.eval Q.rep f = 0) →
    (∀ Q ∈ Y, MvPolynomial.eval Q.rep f = 0)

/-- A projective rational map $\varphi: X \dashrightarrow Y$ is dominant iff its image is Zariski-dense in $Y$. -/
def ProjectiveRationalMap.IsDominant
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) : Prop :=
  IsZariskiDenseIn k (φ.image k) Y

end ProjectiveRegularFunction
end
