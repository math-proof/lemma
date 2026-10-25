import Mathlib
import sympy.Basic
import Lemma.GaloisRep.AdZero
import Def.Deformations_TaylorWilesLocal
set_option autoImplicit false


variable {k : Type} [Field k]


/--
[ker_trace_eq_comap_traceZero]
-/
@[path]
private lemma main
-- given
  (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) :
-- imply
  LinearMap.ker (LinearMap.trace k ρbar.V) =
    (TaylorWiles.traceZero k).comap (LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k).toLinearMap := by
-- proof
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, TaylorWiles.mem_traceZero_iff, LinearEquiv.coe_coe,
    LinearMap.trace_eq_matrix_trace k b f, Matrix.trace, Matrix.diag]


-- created on 2026-10-24
