import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq.lean)
-/
@[main]
private lemma main
  {S : Type u} [CommRing S]
  {S' : Type u} [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
  {k : Type u} [Field k]
  {sk : S →+* k} :
-- imply
  ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (j : k →+* K) (sK : S' →+* K),
      sK.comp (algebraMap S S') = j.comp sk := by
-- proof
  classical
  let : Algebra S k := sk.toAlgebra

  let R : Type u := k ⊗[S] S'
  have : Nontrivial R := Module.FaithfullyFlat.rTensor_nontrivial S S' k
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let K : Type u := AlgebraicClosure (R ⧸ m)
  let π : R →+* K := (algebraMap (R ⧸ m) K).comp (Ideal.Quotient.mk m)
  refine ⟨K, inferInstance, inferInstance, π.comp (algebraMap k R),
    π.comp (Algebra.TensorProduct.includeRight : S' →ₐ[S] R).toRingHom, ?_⟩
  ext s
  change π (Algebra.TensorProduct.includeRight (R := S) (A := k) (B := S') (algebraMap S S' s)) =
    π (algebraMap k R (sk s))
  congr 1
  rw [AlgHom.commutes]
  change algebraMap S R s = algebraMap k R (algebraMap S k s)
  exact (IsScalarTower.algebraMap_apply S k R s)


-- created on 2026-10-05
