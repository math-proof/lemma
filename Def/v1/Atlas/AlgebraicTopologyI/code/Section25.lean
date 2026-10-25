/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import Theorem.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber
open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace TensorChainComplex

variable (R : Type) [CommRing R]

/-- The tensor product of two chain complexes of $R$-modules, with the Leibniz
differential
$d(x \otimes y) = dx \otimes y + (-1)^{|x|} x \otimes dy$.
This is the algebraic side of the Künneth formula. -/
def tensorChainComplex
    (C D : ChainComplex (ModuleCat R) ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  HomologicalComplex.tensorObj C D

/-- The canonical inclusion of the bidegree $(p,q)$ summand $C_p \otimes D_q$ into the
total complex $(C \otimes D)_n$ for $p + q = n$. -/
def ιTensorChainComplex
    (C D : ChainComplex (ModuleCat R) ℕ)
    (p q n : ℕ) (h : p + q = n) :
    (C.X p ⊗ D.X q) ⟶ (tensorChainComplex R C D).X n :=
  HomologicalComplex.ιTensorObj C D p q n h

end TensorChainComplex
end
