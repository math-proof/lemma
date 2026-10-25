/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.NumberTheoryI.code.Chapter4.TensorSplitting
open Polynomial TensorProduct


noncomputable section

namespace TensorSplitting

def quotientInfAlgEquivPiQuotient
    {K' : Type*} [Field K'] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (I : ι → Ideal (Polynomial K'))
    (hc : Pairwise fun i j => IsCoprime (I i) (I j)) :
    (Polynomial K' ⧸ ⨅ i, I i) ≃ₐ[K'] (∀ i, Polynomial K' ⧸ I i) :=
  AlgEquiv.ofRingEquiv (f := Ideal.quotientInfRingEquivPiQuotient I hc)
    (quotientInfRingEquivPiQuotient_algebraMap I hc)

def adjoinRootProdAlgEquiv {K' : Type*} [Field K'] {ι : Type*} [DecidableEq ι]
    [Fintype ι] (g : ι → Polynomial K')
    (hc : Pairwise fun i j => IsCoprime (g i) (g j)) :
    AdjoinRoot (∏ i, g i) ≃ₐ[K'] ∀ i, AdjoinRoot (g i) :=
  (Ideal.quotientEquivAlgOfEq K' (span_prod_eq_iInf g hc)).trans
    (quotientInfAlgEquivPiQuotient (fun i => Ideal.span {g i})
      (fun _ _ hij => (Ideal.isCoprime_span_singleton_iff _ _).mpr (hc hij)))

def adjoinRootProdAlgEquiv_of_irreducible {K' : Type*} [Field K'] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (g : ι → Polynomial K') (hirr : ∀ i, Irreducible (g i))
    (hne : Pairwise fun i j => ¬Associated (g i) (g j)) :
    AdjoinRoot (∏ i, g i) ≃ₐ[K'] ∀ i, AdjoinRoot (g i) :=
  adjoinRootProdAlgEquiv g
    (fun _ _ hij => isCoprime_of_irreducible_of_not_associated (hirr _) (hirr _) (hne hij))

end TensorSplitting
end
