/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber

@[expose] public section

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
