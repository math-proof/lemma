/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.NumberTheoryI.code.Chapter4.TensorSplitting.Part2
open Polynomial TensorProduct


noncomputable section

namespace TensorSplitting

def adjoinRoot_tensorProduct_algEquiv
    {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (f : Polynomial K) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
    (AdjoinRoot f ⊗[K] K') ≃ₐ[K'] AdjoinRoot (Polynomial.map (algebraMap K K') f) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')

  let e1 : (AdjoinRoot f ⊗[K] K') ≃ₐ[K'] K' ⊗[K] AdjoinRoot f :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm K (AdjoinRoot f) K').toRingEquiv)
      (fun k' => by
        show (Algebra.TensorProduct.comm K (AdjoinRoot f) K') (1 ⊗ₜ[K] k') = k' ⊗ₜ[K] 1
        simp [Algebra.TensorProduct.comm_tmul])

  let e2 : K' ⊗[K] AdjoinRoot f ≃ₐ[K']
      (K' ⊗[K] Polynomial K) ⧸
        Ideal.map (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K))
          (Ideal.span {f}) :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := K) K' (Polynomial K) K' (Ideal.span {f})

  have hideal : Ideal.map ((polyEquivTensor' K K').symm : K' ⊗[K] Polynomial K →+* Polynomial K')
      (Ideal.map (↑(Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K))
        : Polynomial K →+* K' ⊗[K] Polynomial K)
        (Ideal.span {f})) =
      Ideal.span {Polynomial.map (algebraMap K K') f} := by
    rw [Ideal.map_map, polyEquivTensor'_symm_comp_includeRight, Ideal.map_span,
      Set.image_singleton]
    rfl
  let e3 : ((K' ⊗[K] Polynomial K) ⧸
      Ideal.map (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Polynomial K))
        (Ideal.span {f})) ≃ₐ[K']
      AdjoinRoot (Polynomial.map (algebraMap K K') f) :=
    (Ideal.quotientEquivAlg _ _ (polyEquivTensor' K K').symm rfl).trans
      (Ideal.quotientEquivAlgOfEq K' hideal)
  exact e1.trans (e2.trans e3)

def adjoinRoot_tensor_algEquiv_prod {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (f : Polynomial K) (_hf_irr : Irreducible f) (_hf_sep : f.Separable)
    (g : ι → Polynomial K') (hirr : ∀ i, Irreducible (g i))
    (hne : Pairwise fun i j => ¬Associated (g i) (g j))
    (hprod : Associated (Polynomial.map (algebraMap K K') f) (∏ i, g i)) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
    (AdjoinRoot f ⊗[K] K') ≃ₐ[K'] ∀ i, AdjoinRoot (g i) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := AdjoinRoot f) (B := K')
  exact (adjoinRoot_tensorProduct_algEquiv f).trans
    ((Ideal.quotientEquivAlgOfEq K'
        (Ideal.span_singleton_eq_span_singleton.mpr hprod) :
        AdjoinRoot (Polynomial.map (algebraMap K K') f) ≃ₐ[K']
          AdjoinRoot (∏ i, g i)).trans
      (adjoinRootProdAlgEquiv_of_irreducible g hirr hne))

end TensorSplitting
end
