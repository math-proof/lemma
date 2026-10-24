import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS
open ManifoldWedgeHelpers
open scoped Manifold ContDiff
open VectorField


namespace ManifoldWedgeHelpers

/--
[oneFormToCL_apply_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma oneFormToCL_apply_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {w : E [⋀^Fin 1]→L[ℝ] ℝ}
  {v : E} :
-- imply
  oneFormToCL w v = w (Matrix.vecCons v Fin.elim0) := by
-- proof
  simp only [oneFormToCL, ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply]
  congr 1; ext ⟨i, hi⟩; interval_cases i; simp [Matrix.vecCons]

end ManifoldWedgeHelpers

namespace ManifoldWedgeHelpers

/--
[curryLeft_alternatizeUncurryFin_smulRight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma curryLeft_alternatizeUncurryFin_smulRight
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {m : ℕ}
  {L : E →L[ℝ] ℝ}
  {β : E [⋀^Fin (m + 1)]→L[ℝ] ℝ}
  {v : E} :
-- imply
  (ContinuousAlternatingMap.alternatizeUncurryFin (L.smulRight β)).curryLeft v = L v • β - ContinuousAlternatingMap.alternatizeUncurryFin (L.smulRight (β.curryLeft v)) := by
-- proof
  ext w
  simp only [ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero]
  have h0 : Fin.removeNth 0 (Matrix.vecCons v w) = w := by
    ext k; simp [Fin.removeNth, Matrix.cons_val_succ]
  rw [h0]
  have hsucc : ∀ i : Fin (m + 1), (Matrix.vecCons v w) i.succ = w i :=
    fun i => Matrix.cons_val_succ v w i
  have hrem : ∀ i : Fin (m + 1),
    Fin.removeNth i.succ (Matrix.vecCons v w) = Matrix.vecCons v (Fin.removeNth i w) := by
    intro i; ext k
    simp only [Fin.removeNth, Matrix.vecCons]
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [Fin.succ_succAbove_zero, Fin.cons_zero, Fin.cons_zero]
    · rw [Fin.succ_succAbove_succ, Fin.cons_succ, Fin.cons_succ]; rfl
  simp_rw [hsucc, hrem, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]
end ManifoldWedgeHelpers
open ManifoldWedgeHelpers
section Operations


/--
[manifoldIota_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma manifoldIota_zero
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {X : ManifoldVF I M}
  {p : ℕ} :
-- imply
  manifoldIota I X (0 : ManifoldΩ I M (p + 1)) = 0 := by
-- proof
  ext x
  simp [manifoldIota]

/--
[manifoldIota_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma manifoldIota_add
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {X : ManifoldVF I M}
  {p : ℕ}
  {α β : ManifoldΩ I M (p + 1)} :
-- imply
  manifoldIota I X (α + β) = manifoldIota I X α + manifoldIota I X β := by
-- proof
  ext x
  simp [manifoldIota]

/--
[manifoldIota_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma manifoldIota_smul
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {X : ManifoldVF I M}
  {p : ℕ}
  {r : ℝ}
  {α : ManifoldΩ I M (p + 1)} :
-- imply
  manifoldIota I X (r • α) = r • manifoldIota I X α := by
-- proof
  ext x
  simp [manifoldIota]

/--
[manifoldIota_fMul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma manifoldIota_fMul
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {X : ManifoldVF I M}
  {p : ℕ}
  {f : ManifoldΩ I M 0}
  {α : ManifoldΩ I M (p + 1)} :
-- imply
  manifoldIota I X (manifoldFMul I f α) = manifoldFMul I f (manifoldIota I X α) := by
-- proof
  ext x; simp [manifoldIota, manifoldFMul]

/--
[manifoldIota_wedge1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma manifoldIota_wedge1
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {X : ManifoldVF I M}
  {p : ℕ}
  {w : ManifoldΩ I M 1}
  {α : ManifoldΩ I M (p + 1)} :
-- imply
  manifoldIota I X (manifoldWedge1 I w α) = manifoldFMul I (manifoldIota I X w) α - manifoldWedge1 I w (manifoldIota I X α) := by
-- proof
  funext x
  show (wedgePointwiseGeneral (w x) (α x)).curryLeft (X x) =
    ((w x).curryLeft (X x) Fin.elim0) • (α x) - wedgePointwiseGeneral (w x) ((α x).curryLeft (X x))
  unfold wedgePointwiseGeneral
  rw [curryLeft_alternatizeUncurryFin_smulRight]
  congr 1
  rw [oneFormToCL_apply_eq]
  simp [ContinuousAlternatingMap.curryLeft_apply_apply]

/--
[manifoldIota_wedge1_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma manifoldIota_wedge1_zero
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {X : ManifoldVF I M}
  {w : ManifoldΩ I M 1}
  {g : ManifoldΩ I M 0} :
-- imply
  manifoldIota I X (manifoldWedge1 I w g) = manifoldFMul I (manifoldIota I X w) g := by
-- proof
  funext x; ext u
  show (wedgePointwiseGeneral (w x) (g x)).curryLeft (X x) u =
    ((w x).curryLeft (X x) Fin.elim0) • (g x) u
  unfold wedgePointwiseGeneral
  rw [ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.smul_apply, Matrix.cons_val_zero]
  rw [oneFormToCL_apply_eq]
  have hrem : Fin.removeNth 0 (Matrix.vecCons (X x) u) = u := by
    ext ⟨k, hk⟩; exact Fin.elim0 ⟨k, by omega⟩
  rw [hrem, ContinuousAlternatingMap.curryLeft_apply_apply]

/--
[manifoldFMul_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma manifoldFMul_add_right
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {p : ℕ}
  {f : ManifoldΩ I M 0}
  {α β : ManifoldΩ I M p} :
-- imply
  manifoldFMul I f (α + β) = manifoldFMul I f α + manifoldFMul I f β := by
-- proof
  ext x
  simp [manifoldFMul, smul_add]

/--
[lieBracket_constVF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean)
-/
@[path]
lemma lieBracket_constVF
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {v w : E}
  {x : E} :
-- imply
  lieBracket ℝ (fun _ : E => v) (fun _ : E => w) x = 0 := by
-- proof
  simp [lieBracket, fderiv_const_apply]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]


-- created on 2026-10-23
