import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.EuclideanDFS.Part3
open EuclideanΩ


namespace EuclideanΩ

/--
[add_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma add_apply
  {n p : ℕ}
  {α β : EuclideanΩ n p}
  {x : Eℝ n} :
-- imply
  (α + β) x = α x + β x :=
-- proof
  rfl

end EuclideanΩ

namespace EuclideanΩ

/--
[neg_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma neg_apply'
  {n p : ℕ}
  {α : EuclideanΩ n p}
  {x : Eℝ n} :
-- imply
  (-α) x = -(α x) :=
-- proof
  rfl

end EuclideanΩ

namespace EuclideanΩ

/--
[smul_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma smul_apply'
  {n p : ℕ}
  {r : ℝ}
  {α : EuclideanΩ n p}
  {x : Eℝ n} :
-- imply
  (r • α) x = r • (α x) :=
-- proof
  rfl

end EuclideanΩ

namespace EuclideanΩ

/--
[zero_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma zero_apply'
  {n p : ℕ}
  {x : Eℝ n} :
-- imply
  (0 : EuclideanΩ n p) x = 0 :=
-- proof
  rfl

end EuclideanΩ

namespace EuclideanΩ

/--
[fromCAlt_toCAlt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma fromCAlt_toCAlt
  {n p : ℕ}
  {n p : ℕ}
  {f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ} :
-- imply
  fromCAlt (toCAlt f) = f := by
-- proof
  ext v; rfl

end EuclideanΩ

namespace EuclideanΩ

/--
[toCAlt_fromCAlt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma toCAlt_fromCAlt
  {n p : ℕ}
  {n p : ℕ}
  {g : Eℝ n [⋀^Fin p]→L[ℝ] ℝ} :
-- imply
  toCAlt (fromCAlt g) = g := by
-- proof
  ext v; rfl

end EuclideanΩ

namespace EuclideanΩ

/--
[toCAlt_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma toCAlt_apply
  {n p : ℕ}
  {n p : ℕ}
  {f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ}
  {v : Fin p → Eℝ n} :
-- imply
  toCAlt f v = f v :=
-- proof
  rfl

end EuclideanΩ

namespace EuclideanΩ

variable {n p : ℕ}
/--
[differentiable_toCEuclideanΩ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma differentiable_toCEuclideanΩ {n p : ℕ} (α : EuclideanΩ n p) :
  Differentiable ℝ (toCEuclideanΩ α) :=
  (contDiff_toCEuclideanΩ α).differentiable (by simp)

end EuclideanΩ

namespace EuclideanΩ

variable {n p : ℕ}
/--
[EuclideanΩ_toCEuclideanΩ_toEuclideanΩ'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma EuclideanΩ_toCEuclideanΩ_toEuclideanΩ' {n p : ℕ}
  (α : EuclideanΩ.CEuclideanΩ n p) :
  toCEuclideanΩ (CEuclideanΩ.toEuclideanΩ' α) = α := by
  apply funext; intro x
  simp [CEuclideanΩ.toEuclideanΩ', toCEuclideanΩ]

end EuclideanΩ

/--
[euclideanFMul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanFMul_apply
  {n p : ℕ}
  {f : EuclideanΩ n 0}
  {α : EuclideanΩ n p}
  {x : Eℝ n} :
-- imply
  euclideanFMul f α x = (f x Fin.elim0) • (α x) :=
-- proof
  rfl

/--
[euclideanIota_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanIota_add
  {n : ℕ}
  {X : EuclideanVF n}
  {p : ℕ}
  {α β : EuclideanΩ n (p + 1)} :
-- imply
  euclideanIota X (α + β) = euclideanIota X α + euclideanIota X β := by
-- proof
  ext x
  simp [euclideanIota]

/--
[euclideanIota_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanIota_smul
  {n : ℕ}
  {X : EuclideanVF n}
  {p : ℕ}
  {r : ℝ}
  {α : EuclideanΩ n (p + 1)} :
-- imply
  euclideanIota X (r • α) = r • euclideanIota X α := by
-- proof
  ext x
  simp [euclideanIota]

/--
[euclideanWedge1_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanWedge1_add_right
  {n : ℕ}
  {ω : EuclideanΩ n 1}
  {p : ℕ}
  {α β : EuclideanΩ n p} :
-- imply
  euclideanWedge1 ω (α + β) = euclideanWedge1 ω α + euclideanWedge1 ω β := by
-- proof
  funext x
  show wedgePointwise (ω x) ((α + β) x) =
    wedgePointwise (ω x) (α x) + wedgePointwise (ω x) (β x)
  simp only [EuclideanΩ.add_apply]
  unfold wedgePointwise
  have h : (oneFormLinear (ω x)).smulRight (α x + β x) =
    (oneFormLinear (ω x)).smulRight (α x) + (oneFormLinear (ω x)).smulRight (β x) := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.smulRight_apply, LinearMap.add_apply, smul_add]
  rw [h, AlternatingMap.alternatizeUncurryFin_add]

/--
[euclideanWedge1_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanWedge1_smul_right
  {n : ℕ}
  {ω : EuclideanΩ n 1}
  {p : ℕ}
  {r : ℝ}
  {α : EuclideanΩ n p} :
-- imply
  euclideanWedge1 ω (r • α) = r • euclideanWedge1 ω α := by
-- proof
  funext x
  show wedgePointwise (ω x) ((r • α) x) = r • wedgePointwise (ω x) (α x)
  simp only [EuclideanΩ.smul_apply']
  unfold wedgePointwise
  have h : (oneFormLinear (ω x)).smulRight (r • α x) =
    r • (oneFormLinear (ω x)).smulRight (α x) := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.smulRight_apply, LinearMap.smul_apply]
    rw [smul_comm]
  rw [h, AlternatingMap.alternatizeUncurryFin_smul]

/--
[euclideanIotaC_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanIotaC_add
  {n : ℕ}
  {X : EuclideanVF n}
  {p : ℕ}
  {α β : EuclideanΩ.CEuclideanΩ n (p + 1)} :
-- imply
  euclideanIotaC X (α + β) = euclideanIotaC X α + euclideanIotaC X β := by
-- proof
  ext x v
  simp only [euclideanIotaC, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]

/--
[euclideanIotaC_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanIotaC_smul
  {n : ℕ}
  {X : EuclideanVF n}
  {p : ℕ}
  {r : ℝ}
  {α : EuclideanΩ.CEuclideanΩ n (p + 1)} :
-- imply
  euclideanIotaC X (r • α) = r • euclideanIotaC X α := by
-- proof
  ext x v
  simp only [euclideanIotaC, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]

namespace EuclideanΩ

/--
[euclideanD_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanD_add
  {n p : ℕ}
  {α β : CEuclideanΩ n p}
-- given
  (hα : Differentiable ℝ α)
  (hβ : Differentiable ℝ β) :
-- imply
  euclideanD (α + β) = euclideanD α + euclideanD β := by
-- proof
  funext x
  show AlternatingMap.alternatizeUncurryFin (fderivToAltMap (α + β) x) =
    AlternatingMap.alternatizeUncurryFin (fderivToAltMap α x) +
    AlternatingMap.alternatizeUncurryFin (fderivToAltMap β x)
  have hfA : fderivToAltMap (α + β) x = fderivToAltMap α x + fderivToAltMap β x := by
    ext h w
    simp only [fderivToAltMap, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      LinearMap.add_apply, fderiv_add (hα x) (hβ x), ContinuousLinearMap.add_apply,
      map_add]
  rw [hfA, AlternatingMap.alternatizeUncurryFin_add]

end EuclideanΩ

namespace EuclideanΩ

/--
[euclideanD_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanD_smul
  {n p : ℕ}
  {r : ℝ}
  {α : CEuclideanΩ n p}
-- given
  (hα : Differentiable ℝ α) :
-- imply
  euclideanD (r • α) = r • euclideanD α := by
-- proof
  funext x
  show AlternatingMap.alternatizeUncurryFin (fderivToAltMap (r • α) x) =
    r • AlternatingMap.alternatizeUncurryFin (fderivToAltMap α x)
  have hfA : fderivToAltMap (r • α) x = r • fderivToAltMap α x := by
    ext h w
    simp only [fderivToAltMap, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      LinearMap.smul_apply, fderiv_const_smul (hα x) r, ContinuousLinearMap.smul_apply,
      map_smul]
  rw [hfA, AlternatingMap.alternatizeUncurryFin_smul]

end EuclideanΩ

/--
[euclideanFMul_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanFMul_add_left
  {n : ℕ}
  {p : ℕ}
  {f g : EuclideanΩ n 0}
  {α : EuclideanΩ n p} :
-- imply
  euclideanFMul (f + g) α = euclideanFMul f α + euclideanFMul g α := by
-- proof
  funext x; ext v
  simp only [euclideanFMul_apply, EuclideanΩ.add_apply, AlternatingMap.add_apply,
    AlternatingMap.smul_apply]
  exact add_smul _ _ _

/--
[euclideanFMul_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanFMul_add_right
  {n : ℕ}
  {p : ℕ}
  {f : EuclideanΩ n 0}
  {α β : EuclideanΩ n p} :
-- imply
  euclideanFMul f (α + β) = euclideanFMul f α + euclideanFMul f β := by
-- proof
  funext x; ext v
  simp only [euclideanFMul_apply, EuclideanΩ.add_apply, AlternatingMap.add_apply,
    AlternatingMap.smul_apply]
  rw [smul_add]

/--
[euclideanFMul_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanFMul_smul
  {n : ℕ}
  {p : ℕ}
  {r : ℝ}
  {f : EuclideanΩ n 0}
  {α : EuclideanΩ n p} :
-- imply
  euclideanFMul (r • f) α = r • euclideanFMul f α := by
-- proof
  funext x; ext v
  simp only [euclideanFMul_apply, EuclideanΩ.smul_apply', AlternatingMap.smul_apply]
  exact smul_assoc _ _ _

/--
[euclideanIota_fMul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanIota_fMul
  {n : ℕ}
  {X : EuclideanVF n}
  {p : ℕ}
  {f : EuclideanΩ n 0}
  {α : EuclideanΩ n (p + 1)} :
-- imply
  euclideanIota X (euclideanFMul f α) = euclideanFMul f (euclideanIota X α) := by
-- proof
  funext x; ext v
  simp only [euclideanIota, euclideanFMul_apply, AlternatingMap.smul_apply]
  rfl

/--
[euclideanD_lifted_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanD_lifted_add
  {n : ℕ}
  {α β : EuclideanΩ n p} :
-- imply
  euclideanD_lifted (α + β) = euclideanD_lifted α + euclideanD_lifted β := by
-- proof
  unfold euclideanD_lifted
  have h : toCEuclideanΩ (α + β) = toCEuclideanΩ α + toCEuclideanΩ β := by
    funext x; ext v
    simp only [toCEuclideanΩ, Pi.add_apply, toCAlt_apply]
    rfl
  rw [h]
  exact euclideanD_add _ _ (differentiable_toCEuclideanΩ α) (differentiable_toCEuclideanΩ β)

/--
[euclideanD_lifted_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanD_lifted_smul
  {n : ℕ}
  {r : ℝ}
  {α : EuclideanΩ n p} :
-- imply
  euclideanD_lifted (r • α) = r • euclideanD_lifted α := by
-- proof
  unfold euclideanD_lifted
  have h : toCEuclideanΩ (r • α) = r • toCEuclideanΩ α := by
    funext x; ext v
    simp only [toCEuclideanΩ, Pi.smul_apply, toCAlt_apply]
    rfl
  rw [h]
  exact euclideanD_smul _ _ (differentiable_toCEuclideanΩ α)

/--
[euclideanLie_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanLie_add
  {n : ℕ}
  {X : EuclideanVF n}
  {p : ℕ}
  {α β : EuclideanΩ n p} :
-- imply
  euclideanLie X (α + β) = euclideanLie X α + euclideanLie X β := by
-- proof
  cases p with
  | zero =>
    simp only [euclideanLie]
    rw [euclideanD_lifted_add, euclideanIota_add]
  | succ p =>
    simp only [euclideanLie]
    rw [euclideanIota_add, euclideanD_lifted_add,
      euclideanD_lifted_add, euclideanIota_add]
    abel

/--
[euclideanLie_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanLie_smul
  {n : ℕ}
  {X : EuclideanVF n}
  {p : ℕ}
  {r : ℝ}
  {α : EuclideanΩ n p} :
-- imply
  euclideanLie X (r • α) = r • euclideanLie X α := by
-- proof
  cases p with
  | zero =>
    simp only [euclideanLie]
    rw [euclideanD_lifted_smul, euclideanIota_smul]
  | succ p =>
    simp only [euclideanLie]
    rw [euclideanIota_smul, euclideanD_lifted_smul,
      euclideanD_lifted_smul, euclideanIota_smul, smul_add]

/--
[euclideanD_eq_extDeriv_toAlternatingMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanD_eq_extDeriv_toAlternatingMap
  {n : ℕ}
  {p : ℕ}
  {α : CEuclideanΩ n p}
  {x : Eℝ n} :
-- imply
  euclideanD α x = (extDeriv α x).toAlternatingMap := by
-- proof
  unfold euclideanD fderivToAltMap extDeriv
  rw [ContinuousAlternatingMap.toAlternatingMap_alternatizeUncurryFin]

variable {n : ℕ}
/--
[toCEuclideanΩ_euclideanD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma toCEuclideanΩ_euclideanD {p : ℕ} (α : CEuclideanΩ n p) :
  toCEuclideanΩ (euclideanD α) = extDeriv α := by
  funext x
  simp only [toCEuclideanΩ, euclideanD_eq_extDeriv_toAlternatingMap]
  exact toCAlt_fromCAlt (extDeriv α x)

/--
[euclideanD_lifted_d_squared](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanD_lifted_d_squared
  {n : ℕ}
  {p : ℕ}
  {α : EuclideanΩ n p} :
-- imply
  euclideanD_lifted (euclideanD_lifted α) = 0 := by
-- proof
  unfold euclideanD_lifted
  rw [toCEuclideanΩ_euclideanD]
  have hsmooth : ContDiff ℝ ⊤ (toCEuclideanΩ α) := contDiff_toCEuclideanΩ α
  have h := extDeriv_extDeriv hsmooth le_top
  funext x
  rw [euclideanD_eq_extDeriv_toAlternatingMap]
  change (extDeriv (extDeriv (toCEuclideanΩ α)) x).toAlternatingMap = 0
  rw [show extDeriv (extDeriv (toCEuclideanΩ α)) x = 0 from congr_fun h x]
  simp

/--
[curryLeft_alternatizeUncurryFin_smulRight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma curryLeft_alternatizeUncurryFin_smulRight
  {n : ℕ}
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {m : ℕ}
  {L : M →ₗ[R] R}
  {β : M [⋀^Fin (m + 1)]→ₗ[R] N}
  {v : M} :
-- imply
  (AlternatingMap.alternatizeUncurryFin (L.smulRight β)).curryLeft v = L v • β - AlternatingMap.alternatizeUncurryFin (L.smulRight (β.curryLeft v)) := by
-- proof
  ext w
  simp only [AlternatingMap.curryLeft_apply_apply, AlternatingMap.alternatizeUncurryFin_apply,
    AlternatingMap.sub_apply, AlternatingMap.smul_apply, LinearMap.smulRight_apply]
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

/--
[oneFormLinear_apply_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma oneFormLinear_apply_eq
  {n : ℕ}
  {n : ℕ}
  {ω_x : Eℝ n [⋀^Fin 1]→ₗ[ℝ] ℝ}
  {v : Eℝ n} :
-- imply
  oneFormLinear ω_x v = ω_x (Matrix.vecCons v Fin.elim0) := by
-- proof
  simp only [oneFormLinear, AlternatingMap.ofSubsingleton_symm_apply_apply]
  congr 1
  ext ⟨i, hi⟩
  have : i = 0 := by omega
  subst this
  simp [Matrix.vecCons]

/--
[euclideanIota_wedge1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
lemma euclideanIota_wedge1
  {n : ℕ}
  {n : ℕ}
  {X : EuclideanVF n}
  {p : ℕ}
  {ω : EuclideanΩ n 1}
  {α : EuclideanΩ n (p + 1)} :
-- imply
  euclideanIota X (euclideanWedge1 ω α) = euclideanFMul (euclideanIota X ω) α - euclideanWedge1 ω (euclideanIota X α) := by
-- proof
  funext x
  show (wedgePointwise (ω x) (α x)).curryLeft (X x) =
    ((ω x).curryLeft (X x) Fin.elim0) • (α x) - wedgePointwise (ω x) ((α x).curryLeft (X x))
  unfold wedgePointwise
  rw [curryLeft_alternatizeUncurryFin_smulRight]
  congr 1
  rw [oneFormLinear_apply_eq]
  simp [AlternatingMap.curryLeft_apply_apply]
/-- Generation principle: every $(p+1)$-form $\beta$ on $\mathbb{R}^n$ can be written as a finite
sum $\sum_i f_i \cdot d\alpha_i$ with $f_i$ a $0$-form and $\alpha_i$ a $p$-form. This is the local
analogue of the fact that $\Omega^\bullet$ is generated by $f \cdot dx_{i_1} \wedge \cdots \wedge dx_{i_p}$. -/

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
private lemma ext_eq
  {n p : ℕ}
  {α β : EuclideanΩ n p}
-- given
  (h : ∀ x, α x = β x) :
-- imply
  α = β := by
-- proof
  apply EuclideanΩ.ext h

/--
[AlternatingMap.continuous_of_euclidean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
private lemma continuous_of_euclidean_eq
  {n p : ℕ}
  {n p : ℕ}
  {f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ} :
-- imply
  Continuous (⇑f : (Fin p → Eℝ n) → ℝ) := by
-- proof
  apply EuclideanΩ.AlternatingMap.continuous_of_euclidean f

/--
[differentiable_toCEuclidean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
private lemma differentiable_toCEuclidean_eq
  {n p : ℕ}
  {n p : ℕ}
  {α : EuclideanΩ n p} :
-- imply
  Differentiable ℝ (toCEuclideanΩ α) := by
-- proof
  apply EuclideanΩ.differentiable_toCEuclidean α

/--
[Euclidean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
private lemma Euclidean_eq
  {n p : ℕ}
  {n p : ℕ}
  {α : EuclideanΩ.CEuclideanΩ n p} :
-- imply
  toCEuclideanΩ (CEuclideanΩ.toEuclideanΩ' α) = α := by
-- proof
  apply EuclideanΩ.Euclidean α

/--
[toCEuclidean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean)
-/
@[path]
private lemma toCEuclidean_eq
  {n : ℕ}
  {p : ℕ}
  {α : CEuclideanΩ n p} :
-- imply
  toCEuclideanΩ (euclideanD α) = extDeriv α := by
-- proof
  apply toCEuclidean α


-- created on 2026-10-23
