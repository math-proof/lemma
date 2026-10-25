/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Trace/InvariantSubmodule.lean -/

/-
Author: Muse Code
-/

import Theorem.LinearAlgebra.Trace.InvariantSubmodule
import Lemma.Matrix.Trace.InvariantSubmodule
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-!
# Tests for trace additivity on an invariant submodule
-/


/-- Smoke test with `W = ⊥`: every endomorphism preserves `⊥`. -/
example (e : V →ₗ[K] V) :
    LinearMap.trace K V e =
      LinearMap.trace K ↥(⊥ : Submodule K V)
          (e.restrict (by simp : (⊥ : Submodule K V) ≤ (⊥ : Submodule K V).comap e)) +
        LinearMap.trace K (V ⧸ (⊥ : Submodule K V))
          ((⊥ : Submodule K V).mapQ _ e (by simp)) :=
  LinearMap.trace_eq_trace_restrict_add_trace_mapQ ⊥ e (by simp)

/-- Smoke test with `W = ⊤`: every endomorphism preserves `⊤`. -/
example (e : V →ₗ[K] V) :
    LinearMap.trace K V e =
      LinearMap.trace K ↥(⊤ : Submodule K V)
          (e.restrict (by simp : (⊤ : Submodule K V) ≤ (⊤ : Submodule K V).comap e)) +
        LinearMap.trace K (V ⧸ (⊤ : Submodule K V))
          ((⊤ : Submodule K V).mapQ _ e (by simp)) :=
  LinearMap.trace_eq_trace_restrict_add_trace_mapQ ⊤ e (by simp)

/-- Concrete instance: the first-coordinate span in `Fin 2 → ℚ`, a proper
nonzero submodule invariant under the identity. -/
example :
    LinearMap.trace ℚ (Fin 2 → ℚ) LinearMap.id =
      LinearMap.trace ℚ ↥(Submodule.span ℚ {(Pi.single 0 1 : Fin 2 → ℚ)})
          (LinearMap.id.restrict (by simp)) +
        LinearMap.trace ℚ
          ((Fin 2 → ℚ) ⧸ (Submodule.span ℚ {(Pi.single 0 1 : Fin 2 → ℚ)}))
          ((Submodule.span ℚ {(Pi.single 0 1 : Fin 2 → ℚ)}).mapQ _ LinearMap.id
            (by simp)) :=
  LinearMap.trace_eq_trace_restrict_add_trace_mapQ _ LinearMap.id (by simp)

/-- Trace of the identity on `K × K` along the surjective first projection:
the trace splits as the kernel restriction plus the target trace. -/
example :
    LinearMap.trace K (K × K) LinearMap.id =
      LinearMap.trace K ↥(LinearMap.ker (LinearMap.fst K K K))
          (LinearMap.id.restrict
            (by
              change LinearMap.ker (LinearMap.fst K K K) ≤
                (LinearMap.ker (LinearMap.fst K K K)).comap LinearMap.id
              rw [← LinearMap.ker_comp LinearMap.id (LinearMap.fst K K K)]
              simp)) +
        LinearMap.trace K K LinearMap.id :=
  LinearMap.trace_eq_trace_restrict_ker_add_of_surjective _ LinearMap.id LinearMap.id
    (LinearMap.fst_surjective) (by simp)

