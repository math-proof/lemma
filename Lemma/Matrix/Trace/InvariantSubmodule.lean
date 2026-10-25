import Mathlib
import sympy.Basic
import Theorem.LinearAlgebra.Trace.InvariantSubmodule
open Module.Basis


/--
[LinearMap.trace_eq_trace_restrict_add_trace_mapQ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Trace/InvariantSubmodule.lean)
-/
@[path]
lemma LinearMap.trace_eq_trace_restrict_add_trace_mapQ
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
  let m := Module.Free.ChooseBasisIndex K W
  let bW : Module.Basis m K W := Module.Free.chooseBasis K W
  let n := Module.Free.ChooseBasisIndex K (V ⧸ W)
  let bQ : Module.Basis n K (V ⧸ W) := Module.Free.chooseBasis K (V ⧸ W)
  let b := sumQuot bW bQ
  have := Module.Free.ChooseBasisIndex.fintype K W
  have := Module.Free.ChooseBasisIndex.fintype K (V ⧸ W)
  let A : Matrix m m K := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n K := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n K := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  have hblock : LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D := by
    ext u v
    cases u with
    | inl i =>
      cases v with
      | inl k =>
        simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
          LinearMap.toMatrix_apply]
        apply sumQuot_repr_inl_of_mem
      | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr j =>
      cases v with
      | inl k =>
        suffices W.mkQ (e (bW k)) = 0 by
          simp [LinearMap.toMatrix_apply, b, this]
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact he (Submodule.coe_mem (bW k))
      | inr l =>
        simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
          Matrix.fromBlocks_apply₂₂, b, D]
        rw [← sumQuot_inr bW bQ l, W.mapQ_apply]
        simp
  have htrace : Matrix.trace (Matrix.fromBlocks A B 0 D) =
    Matrix.trace A + Matrix.trace D := by
    simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  rw [LinearMap.trace_eq_matrix_trace K b e,
    LinearMap.trace_eq_matrix_trace K bW (e.restrict he),
    LinearMap.trace_eq_matrix_trace K bQ (W.mapQ W e he), hblock, htrace]
variable {W : Type*} [AddCommGroup W] [Module K W]

/--
[LinearMap.trace_eq_trace_restrict_ker_add_of_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Trace/InvariantSubmodule.lean)
-/
@[path]
lemma LinearMap.trace_eq_trace_restrict_ker_add_of_surjective
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
  let hi : LinearMap.ker q ≤ (LinearMap.ker q).comap f := by
    rw [← LinearMap.ker_comp f q, h]
    exact LinearMap.ker_le_ker_comp q g
  let E := q.quotKerEquivOfSurjective hq
  have hc : E.conj ((LinearMap.ker q).mapQ (LinearMap.ker q) f hi) = g := by
    ext y
    obtain ⟨x, rfl⟩ := hq y
    simp only [E, LinearEquiv.conj_apply_apply,
      LinearMap.quotKerEquivOfSurjective_symm_apply,
      Submodule.mapQ_apply,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
    exact LinearMap.congr_fun h x
  rw [LinearMap.trace_eq_trace_restrict_add_trace_mapQ
    (LinearMap.ker q) f hi,
    ← LinearMap.trace_conj'
      ((LinearMap.ker q).mapQ (LinearMap.ker q) f hi) E, hc]


-- created on 2026-10-20
-- updated on 2026-10-23
