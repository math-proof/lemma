import Mathlib
import Initialize.Tactic.Attr.Basic
open IsModuleTopology


@[path]
private lemma main
  [TopologicalSpace R]
  [CommSemiring R]
  [AddCommMonoid A]
  [Module R A]
  [TopologicalSpace A]
  [IsModuleTopology R A]
  [AddCommMonoid B]
  [Module R B]
  [TopologicalSpace B]
  [IsModuleTopology R B]
  [AddCommMonoid C]
  [Module R C]
  [TopologicalSpace C]
  [IsModuleTopology R C]
  [IsTopologicalSemiring R]
  [Module.Finite R A]
  [Module.Free R A]
-- given
  (bil : A →ₗ[R] B →ₗ[R] C) :
-- imply
  Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
-- proof
  let ι := Module.Free.ChooseBasisIndex R A
  let hι : Fintype ι := Module.Free.ChooseBasisIndex.fintype R A
  let b : Module.Basis ι R A := Module.Free.chooseBasis R A
  let elinear : A ≃ₗ[R] (ι → R) := b.equivFun
  let bil' : (ι → R) →ₗ[R] B →ₗ[R] C := bil.comp elinear.symm.toLinearMap
  have := continuous_bilinear_of_pi_fintype ι bil'
  have foo : (fun ab ↦ (bil ab.1) ab.2 : A × B → C) = (fun fb ↦ bil' fb.1 fb.2) ∘
    (fun ab ↦ (elinear ab.1, ab.2) : A × B → (ι → R) × B) := by
    ext ⟨a, b⟩
    simp [bil']
  rw [foo]
  apply Continuous.comp this
  apply Continuous.prodMk
  · apply continuous_of_linearMap (elinear.toLinearMap.comp (LinearMap.fst R A B))
  · fun_prop


-- created on 2026-11-13
