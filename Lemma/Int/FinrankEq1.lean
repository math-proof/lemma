import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Flat R P]
  (K : Type u) [Field K] [Algebra R K]
  -- given
  (h : ∀ 𝔭, Module.rankAtStalk (R := R) P 𝔭 = 1) :
  -- imply
  Module.finrank K (TensorProduct R K P) = 1 := by
  -- proof
  have hq : Module.rankAtStalk (R := K) (TensorProduct R K P) ⟨⊥, Ideal.isPrime_bot⟩ = 1 := by
    rw [Module.rankAtStalk_baseChange]
    apply h _
  rw [Module.rankAtStalk_eq_finrank_tensorProduct] at hq
  let _ : Nontrivial (Localization.AtPrime (⊥ : Ideal K)) := by
    infer_instance
  rwa [Module.finrank_baseChange] at hq


-- created on 2026-10-20
