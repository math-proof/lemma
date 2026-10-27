import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S]
  (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S'] [Algebra.FiniteType S S']
  (k : Type u) [Field k] [IsAlgClosed k]
  (sk : RingHom S k) :
  -- imply
  ∃ σ : RingHom S' k, σ.comp (algebraMap S S') = sk := by
  -- proof
  classical
  let _ : Algebra S k := sk.toAlgebra
  have hsk : algebraMap S k = sk := rfl
  let B := TensorProduct S k S'
  let _ : Nontrivial B := Module.FaithfullyFlat.rTensor_nontrivial S S' k
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  let _ : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let _ : Algebra.FiniteType k B := inferInstance
  let _ : Algebra.FiniteType k (B ⧸ 𝔪) := inferInstance
  let _ : Module.Finite k (B ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ 𝔪)
  let _ : Algebra.IsAlgebraic k (B ⧸ 𝔪) := inferInstance
  let _ : Module.Free k (B ⧸ 𝔪) := Module.Free.of_divisionRing k (B ⧸ 𝔪)
  let _ : Module.Flat k (B ⧸ 𝔪) := inferInstance
  let _ : Module.IsTorsionFree k (B ⧸ 𝔪) := inferInstance
  let ψ : AlgHom k (B ⧸ 𝔪) k := IsAlgClosed.lift
  let σ : RingHom S' k := ψ.toRingHom.comp ((Ideal.Quotient.mk 𝔪).comp
    (Algebra.TensorProduct.includeRight (R := S) (A := k) (B := S')).toRingHom)
  refine ⟨σ, ?_⟩
  ext s
  have h1 : (Algebra.TensorProduct.includeRight (R := S) (A := k) (B := S')) (algebraMap S S' s) =
      algebraMap k B (sk s) := by
    show TensorProduct.tmul S (1 : k) (algebraMap S S' s) = algebraMap k (TensorProduct S k S') (sk s)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one (A := S') s, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one, hsk]
  show ψ (Ideal.Quotient.mk 𝔪 ((Algebra.TensorProduct.includeRight (R := S) (A := k) (B := S'))
    (algebraMap S S' s))) = sk s
  rw [h1]
  apply ψ.commutes (sk s)


-- created on 2026-10-20
