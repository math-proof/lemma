import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
open StatMech StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[norm_sub_sq_le_pathLength_mul_sum_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma norm_sub_sq_le_pathLength_mul_sum_dist_eq
  {F : Complex → Complex}
  {gamma : Nat → Complex}
  {steps : Nat}
  {C : Real}
-- given
  (hstep : ∀ k < steps, ‖F (gamma k) - F (gamma (k + 1))‖ ^ 2 ≤ C * dist (gamma k) (gamma (k + 1))) :
-- imply
  ‖F (gamma 0) - F (gamma steps)‖ ^ 2 ≤ (steps : Real) * C * ∑ k ∈ Finset.range steps, dist (gamma k) (gamma (k + 1)) := by
-- proof
  apply StatMech.Universality.norm_sub_sq_le_pathLength_mul_sum_dist F gamma steps C hstep

/--
[norm_sub_sq_le_pathLength_sq_mul_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma norm_sub_sq_le_pathLength_sq_mul_mesh_eq
  {F : Complex → Complex}
  {gamma : Nat → Complex}
  {steps : Nat}
  {C mesh : Real}
-- given
  (hC : 0 ≤ C)
  (hstepDist : ∀ k < steps, dist (gamma k) (gamma (k + 1)) ≤ mesh)
  (hstepHolder : ∀ k < steps, ‖F (gamma k) - F (gamma (k + 1))‖ ^ 2 ≤ C * dist (gamma k) (gamma (k + 1))) :
-- imply
  ‖F (gamma 0) - F (gamma steps)‖ ^ 2 ≤ C * (steps : Real) ^ 2 * mesh := by
-- proof
  apply StatMech.Universality.norm_sub_sq_le_pathLength_sq_mul_mesh F gamma steps C mesh hC hstepDist hstepHolder

/--
[constantRadialTensorTent_boundaryPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma constantRadialTensorTent_boundaryPoint_eq
  {k : Nat} :
-- imply
  constantRadialTensorTent k (constantRadialTensorTentBoundaryPoint k) = 1 := by
-- proof
  apply StatMech.Universality.constantRadialTensorTent_boundaryPoint k

/--
[constantRadialTensorTent_cellPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma constantRadialTensorTent_cellPoint_eq
  {k i j : Nat}
  {x y : Real}
-- given
  (hi : i + 1 < k + 2)
  (hj : j + 1 < k + 2)
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1) :
-- imply
  constantRadialTensorTent k (isingRadialGridCellPoint (1 / (k + 2 : Real)) i j x y) = 1 := by
-- proof
  apply StatMech.Universality.constantRadialTensorTent_cellPoint k i j hi hj x y hx0 hx1 hy0 hy1

/--
[constantRadialTensorTent_exteriorPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma constantRadialTensorTent_exteriorPoint_eq
  {k : Nat} :
-- imply
  constantRadialTensorTent k (constantRadialTensorTentExteriorPoint k) = 0 := by
-- proof
  apply StatMech.Universality.constantRadialTensorTent_exteriorPoint k

/--
[constantRadialTensorTent_points_tendsto_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma constantRadialTensorTent_points_tendsto_same_eq :
-- imply
  Tendsto (fun k ↦ dist (constantRadialTensorTentBoundaryPoint k) (constantRadialTensorTentExteriorPoint k)) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.constantRadialTensorTent_points_tendsto_same

/--
[constantRadialTensorTent_not_meshUniformFullHolder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma constantRadialTensorTent_not_meshUniformFullHolder_eq :
-- imply
  ¬ Nonempty (FKIsingCaratheodoryApproximation.MeshUniformFullHolder constantRadialTensorTent) := by
-- proof
  apply StatMech.Universality.constantRadialTensorTent_not_meshUniformFullHolder

/--
[MeshUniformCompactHolder.equicontinuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma equicontinuousOn_eq
  {A : FKIsingCaratheodoryApproximation}
  {F : Nat → Complex → Complex}
  {H : A.MeshUniformCompactHolder F}
  {K : Set Complex}
-- given
  (hK : IsCompact K)
  (hKU : K ⊆ A.U) :
-- imply
  EquicontinuousOn F K := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.MeshUniformCompactHolder.equicontinuousOn A H K hK hKU

/--
[StableFullMedialInterpolation.hasCompactLocalBounds_of_compactHolder_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma hasCompactLocalBounds_of_compactHolder_anchor_eq
  {A : FKIsingCaratheodoryApproximation}
  {tangent : ∀ n, A.M n → Complex}
  {I : A.StableFullMedialInterpolation tangent}
  {H : A.MeshUniformCompactHolder I.interpolant}
  {B : Real}
-- given
  (hanchor : ∀ n, ‖I.interpolant n A.root‖ ≤ B) :
-- imply
  I.HasCompactLocalBounds := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableFullMedialInterpolation.hasCompactLocalBounds_of_compactHolder_anchor A I H B hanchor

/--
[StableFullMedialInterpolation.scalingLimit_of_tensorTentCompactHolder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean)
-/
@[path]
private lemma scalingLimit_of_tensorTentCompactHolder_eq
  {A : FKIsingCaratheodoryApproximation}
  {tangent : ∀ n, A.M n → Complex}
  {I : A.StableFullMedialInterpolation tangent}
  {H : A.MeshUniformCompactHolder I.interpolant}
  {B : Real}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion A.U}
-- given
  (hanchorBound : ∀ n, ‖I.interpolant n A.root‖ ≤ B)
  (htarget : DifferentiableOn Complex target A.U)
  (htarget_ne : target A.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi A.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) A.U)
  (hidentify : StableFullMedialInterpolation.SubsequentialMoreraPrimitive A I target Phi) :
-- imply
  TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableFullMedialInterpolation.scalingLimit_of_tensorTentCompactHolder A I H B hanchorBound target Phi htarget htarget_ne hPhi hPhideriv E hidentify


-- created on 2026-10-23
