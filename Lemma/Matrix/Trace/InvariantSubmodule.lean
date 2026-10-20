import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Trace.InvariantSubmodule
open Module.Basis


/--
[LinearMap.trace_eq_trace_restrict_add_trace_mapQ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Trace/InvariantSubmodule.lean)
-/
@[path]
private lemma LinearMap_trace_eq_trace_restrict_add_trace_mapQ_eq
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Submodule K V}
  {e : V →ₗ[K] V}
-- given
  (he : W ≤ W.comap e) :
-- imply
  LinearMap.trace K V e =
    LinearMap.trace K W (e.restrict he) +
    LinearMap.trace K (V ⧸ W) (W.mapQ W e he) := by
-- proof
  apply LinearMap.trace_eq_trace_restrict_add_trace_mapQ W e he

/--
[LinearMap.trace_eq_trace_restrict_ker_add_of_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Trace/InvariantSubmodule.lean)
-/
@[path]
private lemma LinearMap_trace_eq_trace_restrict_ker_add_of_surjective_eq
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
  {q : V →ₗ[K] W}
  {f : V →ₗ[K] V}
  {g : W →ₗ[K] W}
-- given
  (hq : Function.Surjective q)
  (h : q.comp f = g.comp q) :
-- imply
  LinearMap.trace K V f =
    LinearMap.trace K (LinearMap.ker q)
    (f.restrict (by
    change LinearMap.ker q ≤ (LinearMap.ker q).comap f
    rw [← LinearMap.ker_comp f q, h]
    exact LinearMap.ker_le_ker_comp q g)) +
    LinearMap.trace K W g := by
-- proof
  apply LinearMap.trace_eq_trace_restrict_ker_add_of_surjective q f g hq h


-- created on 2026-10-20
