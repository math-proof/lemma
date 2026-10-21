import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

/--
[HopfOrder_integralClosure_finite_of_etale](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfOrder_integralClosure_finite_of_etale.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type w} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A] :
  -- imply
  Module.Finite R ↥(integralClosure R A) := by
  -- proof
  classical
  obtain ⟨I, hIfin, F, hF, hFK, e, hsep⟩ := (Algebra.FormallyEtale.iff_exists_algEquiv_prod K A).mp inferInstance
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Module.Free K A := Module.Free.of_divisionRing K A
  let _ : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  let algRF : ∀ i, Algebra R (F i) := fun i => ((algebraMap K (F i)).comp (algebraMap R K)).toAlgebra
  let towRF : ∀ i, IsScalarTower R K (F i) := fun i => IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let π : ∀ i, AlgHom K A (F i) := fun i => (Pi.evalAlgHom K F i).comp e.toAlgHom
  have hπsurj : ∀ i, Function.Surjective (π i) := by
    intro i y
    refine ⟨e.symm (Pi.single i y), ?_⟩
    simp [π]
  let finF : ∀ i, Module.Finite K (F i) := fun i => Module.Finite.of_surjective (π i).toLinearMap (hπsurj i)
  let fdF : ∀ i, FiniteDimensional K (F i) := fun i => inferInstance
  let finC : ∀ i, Module.Finite R ↥(integralClosure R (F i)) := fun i => IsIntegralClosure.finite R K (F i) ↥(integralClosure R (F i))
  let Φ : ↥(integralClosure R A) →ₗ[R] (Π i, ↥(integralClosure R (F i))) :=
    { toFun := fun x i => ⟨π i (x : A), by
        apply x.2.map ((π i).restrictScalars R)⟩
      map_add' := by
        intro x y
        funext i
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        funext i
        apply Subtype.ext
        simp [RingHom.id_apply, Pi.smul_apply]
        rw [← IsScalarTower.algebraMap_smul K r (x : A), map_smul, IsScalarTower.algebraMap_smul] }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    funext i
    have hcoe := congrArg (fun f => ((f i : ↥(integralClosure R (F i))) : F i)) hxy
    simp [Φ, π] at hcoe
    apply hcoe
  refine Module.Finite.of_injective Φ hΦ


-- created on 2026-10-20
