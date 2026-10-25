import Mathlib
import sympy.Basic
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section15
open Topology CWSubcomplex SphereInfty


namespace CWSubcomplex

/--
[isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
lemma isClosed
  [TopologicalSpace X]
  [Topology.CWComplex (Set.univ : Set X)]
  {E : CWSubcomplex X} :
-- imply
  IsClosed (E : Set X) :=
-- proof
  E.closed

end CWSubcomplex

namespace CWSubcomplex

/--
[subset_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
lemma subset_univ
  [TopologicalSpace X]
  [Topology.CWComplex (Set.univ : Set X)]
  {E : CWSubcomplex X} :
-- imply
  (E : Set X) ⊆ Set.univ :=
-- proof
  Set.subset_univ _

end CWSubcomplex

namespace SphereInfty

/--
[Sphere.mem_RInfty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
lemma Sphere.mem_RInfty
  {x : Sphere} :
-- imply
  (x.1 : l2) ∈ RInfty :=
-- proof
  x.2.1

end SphereInfty

namespace SphereInfty

/--
[memℓp_shiftRight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
change the multiset of nonzero values. -/
lemma memℓp_shiftRight {x : ℕ → ℝ} (hx : Memℓp x 2) : Memℓp (shiftRight x) 2 := by
  unfold Memℓp at *
  simp only [two_ne_zero, ENNReal.ofNat_ne_top, ↓reduceIte] at *
  rw [← summable_nat_add_iff 1]; simp only [shiftRight]; exact hx

end SphereInfty

namespace SphereInfty

/--
[T_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
lemma T_sub
  {x y : l2} :
-- imply
  T x - T y = T (x - y) := by
-- proof
  ext n; show (shiftRight x.1 - shiftRight y.1) n = shiftRight (x.1 - y.1) n
  cases n with
  | zero => simp [shiftRight]
  | succ _ => rfl

end SphereInfty

namespace SphereInfty

/--
[T_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
lemma T_isometry
-- imply
  Isometry (T : l2 → l2) := by
-- proof
  rw [isometry_iff_dist_eq]; intro x y
  rw [dist_eq_norm, dist_eq_norm, T_sub, T_norm]

end SphereInfty

namespace SphereInfty

/--
[continuous_T](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
lemma continuous_T
-- imply
  Continuous (T : l2 → l2) :=
-- proof
  T_isometry.continuous

end SphereInfty

/--
[RInfty.add_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma add_mem_eq
  {x y : l2}
-- given
  (hx : x ∈ RInfty)
  (hy : y ∈ RInfty) :
-- imply
  x + y ∈ RInfty := by
-- proof
  apply SphereInfty.RInfty.add_mem hx hy

/--
[RInfty.smul_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma smul_mem_eq
  {c : ℝ}
  {x : l2}
-- given
  (hx : x ∈ RInfty) :
-- imply
  c • x ∈ RInfty := by
-- proof
  apply SphereInfty.RInfty.smul_mem c hx

/--
[norm_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma norm_eq_one_eq
  {x : Sphere} :
-- imply
  ‖(x.1 : l2)‖ = 1 := by
-- proof
  apply SphereInfty.norm_eq_one x

/--
[finite_support_shiftRight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma finite_support_shiftRight_eq
  {x : ℕ → ℝ}
-- given
  (hx : Set.Finite (Function.support x)) :
-- imply
  Set.Finite (Function.support (shiftRight x)) := by
-- proof
  apply SphereInfty.finite_support_shiftRight hx

/--
[mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma mem_eq
  {x : ℕ → ℝ}
-- given
  (hx : Memℓp x 2) :
-- imply
  Memℓp (shiftRight x) 2 := by
-- proof
  apply SphereInfty.mem hx

/--
[T_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma T_norm_eq
  {x : l2} :
-- imply
  ‖T x‖ = ‖x‖ := by
-- proof
  apply SphereInfty.T_norm x

/--
[T_mem_RInfty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma T_mem_RInfty_eq
  {x : l2}
-- given
  (hx : x ∈ RInfty) :
-- imply
  T x ∈ RInfty := by
-- proof
  apply SphereInfty.T_mem_RInfty hx

/--
[T_mem_sphere_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma T_mem_sphere_set_eq
  {x : Sphere} :
-- imply
  T x.1 ∈ RInfty ∩ Metric.sphere (0 : l2) 1 := by
-- proof
  apply SphereInfty.T_mem_sphere_set x

/--
[shiftRight_affine_zero_imp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma shiftRight_affine_zero_imp_eq
  {x : ℕ → ℝ}
  {t : ℝ}
-- given
  (ht : 0 < t)
  (h : ∀ n, t * x n + (1 - t) * shiftRight x n = 0) :
-- imply
  ∀ n, x n = 0 := by
-- proof
  apply SphereInfty.shiftRight_affine_zero_imp ht h

/--
[norm_affine_id_T_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma norm_affine_id_T_pos_eq
  {x : l2}
  {t : ℝ}
-- given
  (hx : ‖x‖ = 1)
  (ht0 : 0 ≤ t)
  (_ : t ≤ 1) :
-- imply
  0 < ‖t • x + (1 - t) • T x‖ := by
-- proof
  apply SphereInfty.norm_affine_id_T_pos x hx t ht0 _

/--
[e1_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma e1_norm_eq :
-- imply
  ‖e1‖ = 1 := by
-- proof
  apply SphereInfty.e1_norm

/--
[e1_mem_RInfty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma e1_mem_RInfty_eq :
-- imply
  e1 ∈ RInfty := by
-- proof
  apply SphereInfty.e1_mem_RInfty

/--
[e1_mem_sphere_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma e1_mem_sphere_set_eq :
-- imply
  e1 ∈ RInfty ∩ Metric.sphere (0 : l2) 1 := by
-- proof
  apply SphereInfty.e1_mem_sphere_set

/--
[norm_affine_T_e1_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma norm_affine_T_e1_pos_eq
  {x : l2}
  {t : ℝ}
-- given
  (hx : ‖x‖ = 1)
  (_ : 0 ≤ t)
  (ht1 : t ≤ 1) :
-- imply
  0 < ‖t • T x + (1 - t) • e1‖ := by
-- proof
  apply SphereInfty.norm_affine_T_e1_pos x hx t _ ht1

/--
[continuous_normalize_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma continuous_normalize_comp_eq
  [TopologicalSpace α]
  {v : α → l2}
-- given
  (hv_cont : Continuous v)
  (hv_ne : ∀ x, v x ≠ 0) :
-- imply
  Continuous (fun x => ‖v x‖⁻¹ • v x) := by
-- proof
  apply SphereInfty.continuous_normalize_comp v hv_cont hv_ne

/--
[norm_normalize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma norm_normalize_eq
  {v : l2}
-- given
  (hv : v ≠ 0) :
-- imply
  ‖v‖⁻¹ • v ∈ Metric.sphere (0 : l2) 1 := by
-- proof
  apply SphereInfty.norm_normalize v hv

/--
[v_id_T_mem_RInfty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma v_id_T_mem_RInfty_eq
  {p : I × Sphere} :
-- imply
  v_id_T p ∈ RInfty := by
-- proof
  apply SphereInfty.v_id_T_mem_RInfty p

/--
[continuous_v_id_T](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma continuous_v_id_T_eq :
-- imply
  Continuous v_id_T := by
-- proof
  apply SphereInfty.continuous_v_id_T

/--
[v_id_T_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma v_id_T_ne_zero_eq
  {p : I × Sphere} :
-- imply
  v_id_T p ≠ 0 := by
-- proof
  apply SphereInfty.v_id_T_ne_zero p

/--
[v_T_e1_mem_RInfty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma v_T_e1_mem_RInfty_eq
  {p : I × Sphere} :
-- imply
  v_T_e1 p ∈ RInfty := by
-- proof
  apply SphereInfty.v_T_e1_mem_RInfty p

/--
[continuous_v_T_e1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma continuous_v_T_e1_eq :
-- imply
  Continuous v_T_e1 := by
-- proof
  apply SphereInfty.continuous_v_T_e1

/--
[v_T_e1_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean)
-/
@[path]
private lemma v_T_e1_ne_zero_eq
  {p : I × Sphere} :
-- imply
  v_T_e1 p ≠ 0 := by
-- proof
  apply SphereInfty.v_T_e1_ne_zero p


-- created on 2026-10-23
