import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma smulCommClass
  {q : ℕ} [Fact q.Prime]
  {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
  {G : Type} [Group G] [MulSemiringAction G L]
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
  -- imply
  SMulCommClass G ℚ_[q] L :=
  ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG g c]⟩

/--
[ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq.lean)
-/
@[path]
private lemma main
  (q : ℕ) [Fact q.Prime]
  (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
  (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
  -- imply
  ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), K ≤ L ∧ ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x := by
  -- proof
  let _ := smulCommClass hG
  let _ : FiniteDimensional ℚ_[q] (FixedPoints.intermediateField (F := ℚ_[q]) (E := L) G) := IntermediateField.finiteDimensional_left _
  refine ⟨IntermediateField.lift (FixedPoints.intermediateField (F := ℚ_[q]) (E := L) G), LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv (FixedPoints.intermediateField (F := ℚ_[q]) (E := L) G)).toLinearEquiv, IntermediateField.lift_le _, fun x => ?_⟩
  rw [IntermediateField.mem_lift]
  rfl


-- created on 2026-10-20
