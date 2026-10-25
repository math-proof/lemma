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
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part4


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- A projective morphism $X \to Y$: a projective rational map that is regular everywhere on $X$. -/
structure ProjectiveMorphism (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  toRatMap : ProjectiveRationalMap m n k X Y
  is_morphism : toRatMap.IsMorphism k

end ProjectiveRegularFunction
end
