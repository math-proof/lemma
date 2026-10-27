import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


/--
[Algebra.Etale.of_isSemisimpleRing_tensorProduct](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Etale/SemisimpleBaseChange.lean)
-/
@[path]
lemma Algebra.Etale.of_isSemisimpleRing_tensorProduct
  [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [CommRing A] [Algebra K A] [Module.Finite K A]
-- given
  (h : IsSemisimpleRing (Ω ⊗[K] A)) :
-- imply
  Algebra.Etale K A := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-26
