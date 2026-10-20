/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Etale/SemisimpleBaseChange.lean -/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.TensorProduct.Finite

open scoped TensorProduct

/-- A finite algebra over a field is étale when its base change to an algebraically closed
extension is a semisimple ring. -/
theorem Algebra.Etale.of_isSemisimpleRing_tensorProduct
    {K Ω A : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    [CommRing A] [Algebra K A] [Module.Finite K A]
    (h : IsSemisimpleRing (Ω ⊗[K] A)) : Algebra.Etale K A := by
  have : IsSemisimpleRing (Ω ⊗[K] A) := h
  have : Module.Finite Ω (Ω ⊗[K] A) := inferInstance
  have : IsReduced (Ω ⊗[K] A) := inferInstance
  have : IsArtinianRing (Ω ⊗[K] A) := .of_finite Ω _
  have : Algebra.Etale Ω (Ω ⊗[K] A) := by
    rw [Algebra.Etale.iff_exists_algEquiv_prod]
    refine ⟨MaximalSpectrum (Ω ⊗[K] A), inferInstance, fun m ↦
      ((Ω ⊗[K] A) ⧸ m.asIdeal), fun m ↦ Ideal.Quotient.field _,
      inferInstance, (IsArtinianRing.equivPi _).restrictScalars Ω,
      fun m ↦ ?_⟩
    have := Ideal.Quotient.field m.asIdeal
    have : Module.Finite Ω (((Ω ⊗[K] A)) ⧸ m.asIdeal) :=
      .of_surjective (m.asIdeal.mkQ.restrictScalars Ω) m.asIdeal.mkQ_surjective
    exact ⟨inferInstance, inferInstance⟩
  have : Module.FaithfullyFlat K Ω := inferInstance
  exact .of_etale_tensorProduct_of_faithfullyFlat Ω
