import Mathlib
import Lemma.GaloisRep.AdZero
import Def.Deformations_TaylorWilesLocal

set_option autoImplicit false

namespace ResidualGaloisRep

variable {k : Type} [Field k]

theorem ker_trace_eq_comap_traceZero (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) :
    LinearMap.ker (LinearMap.trace k ρbar.V)
      = (TaylorWiles.traceZero k).comap (LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k).toLinearMap := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, TaylorWiles.mem_traceZero_iff, LinearEquiv.coe_coe,
    LinearMap.trace_eq_matrix_trace k b f, Matrix.trace, Matrix.traceLinearMap_apply, Matrix.diag]

noncomputable def adZeroEquivTraceZero (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) :
    LinearMap.ker (LinearMap.trace k ρbar.V) ≃ₗ[k] TaylorWiles.traceZero k :=
  LinearEquiv.ofSubmodules (LinearMap.toMatrix b b) _ _ (by
    rw [ker_trace_eq_comap_traceZero ρbar b, Submodule.map_comap_eq_of_surjective]
    exact (LinearMap.toMatrix b b).surjective)

@[simp]
theorem adZeroEquivTraceZero_apply_coe (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V)
    (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    ((ρbar.adZeroEquivTraceZero b f : TaylorWiles.traceZero k) : Matrix (Fin 2) (Fin 2) k) = LinearMap.toMatrix b b (f : Module.End k ρbar.V) :=
  rfl

end ResidualGaloisRep
