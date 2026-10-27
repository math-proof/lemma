import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part4
open Filter Topology StatMech StatMech.FrontierA


/--
[finiteMarkedSpinCorrelation_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma finiteMarkedSpinCorrelation_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {marked : ι ↪ V}
-- given
  (β h : Real)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ finiteMarkedSpinCorrelation G β h marked := by
-- proof
  apply StatMech.FrontierA.finiteMarkedSpinCorrelation_nonneg G β h hβ hh marked

/--
[finiteMarkedSpinCorrelation_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma finiteMarkedSpinCorrelation_relabel_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {marked : ι ↪ V}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (β h : Real) :
-- imply
  finiteMarkedSpinCorrelation G β h marked = finiteMarkedSpinCorrelation H β h (marked.trans σ.toEmbedding) := by
-- proof
  apply StatMech.FrontierA.finiteMarkedSpinCorrelation_relabel G H σ hσ β h marked

/--
[squareBoxMovingSpinCorrelation_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma squareBoxMovingSpinCorrelation_nonneg_eq
  {ι : Type*}
  [Fintype ι]
  {radius : Nat → Nat}
  {n : Nat}
-- given
  (β h : Real)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (marked : ∀ n, ι ↪ boxVerts 2 (radius n)) :
-- imply
  0 ≤ squareBoxMovingSpinCorrelation ι β h radius marked n := by
-- proof
  apply StatMech.FrontierA.squareBoxMovingSpinCorrelation_nonneg ι β h hβ hh radius marked n

/--
[squareBoxMovingSpinCorrelation_eq_of_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma squareBoxMovingSpinCorrelation_eq_of_relabel_eq
  {ι : Type*}
  [Fintype ι]
  {sourceRadius targetRadius : Nat → Nat}
-- given
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
  (hσ : ∀ n x y, (boxGraph 2 (sourceRadius n)).Adj x y ↔ (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
  (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) :
-- imply
  squareBoxMovingSpinCorrelation ι β h sourceRadius sourceMarked = squareBoxMovingSpinCorrelation ι β h targetRadius targetMarked := by
-- proof
  apply StatMech.FrontierA.squareBoxMovingSpinCorrelation_eq_of_relabel ι β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked

/--
[spinMeshRenormalization_uniformScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma spinMeshRenormalization_uniformScale_eq
  {ι : Type*}
  [Fintype ι]
  {sourceδ targetδ : Real}
-- given
  (hsourceδ : 0 < sourceδ)
  (htargetδ : 0 < targetδ) :
-- imply
  spinMeshRenormalization ι targetδ = (∏ _ : ι, (targetδ / sourceδ) ^ (-isingSpinScalingDimension)) * spinMeshRenormalization ι sourceδ := by
-- proof
  apply StatMech.FrontierA.spinMeshRenormalization_uniformScale ι hsourceδ htargetδ

/--
[squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel_eq
  {ι : Type*}
  [Fintype ι]
  {sourceδ targetδ : Nat → Real}
  {sourceRadius targetRadius : Nat → Nat}
  {n : Nat}
-- given
  (hsourceδ : ∀ n, 0 < sourceδ n)
  (htargetδ : ∀ n, 0 < targetδ n)
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
  (hσ : ∀ n x y, (boxGraph 2 (sourceRadius n)).Adj x y ↔ (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
  (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) :
-- imply
  squareBoxRenormalizedSpinCorrelation ι targetδ β h targetRadius targetMarked n = (∏ _ : ι, (targetδ n / sourceδ n) ^ (-isingSpinScalingDimension)) * squareBoxRenormalizedSpinCorrelation ι sourceδ β h sourceRadius sourceMarked n := by
-- proof
  apply StatMech.FrontierA.squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel ι sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked n

/--
[tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel_eq
  {ι : Type*}
  [Fintype ι]
  {sourceδ targetδ : Nat → Real}
  {sourceRadius targetRadius : Nat → Nat}
  {ρ L : Real}
-- given
  (hsourceδ : ∀ n, 0 < sourceδ n)
  (htargetδ : ∀ n, 0 < targetδ n)
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
  (hσ : ∀ n x y, (boxGraph 2 (sourceRadius n)).Adj x y ↔ (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
  (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i)
  (hρ : 0 < ρ)
  (hratio : Tendsto (fun n ↦ targetδ n / sourceδ n) atTop (nhds ρ))
  (hsource : Tendsto (squareBoxRenormalizedSpinCorrelation ι sourceδ β h sourceRadius sourceMarked) atTop (nhds L)) :
-- imply
  Tendsto (squareBoxRenormalizedSpinCorrelation ι targetδ β h targetRadius targetMarked) atTop (nhds ((∏ _ : ι, ρ ^ (-isingSpinScalingDimension)) * L)) := by
-- proof
  apply StatMech.FrontierA.tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel ι sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked hρ hratio hsource

/--
[deriv_inverseUniformScaleConformalMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma deriv_inverseUniformScaleConformalMap_eq
  {rho : Real}
  {z : Complex} :
-- imply
  deriv (inverseUniformScaleConformalMap rho) z = (rho⁻¹ : Complex) := by
-- proof
  apply StatMech.FrontierA.deriv_inverseUniformScaleConformalMap rho z

/--
[spinConformalFactor_inverseUniformScaleConformalMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma spinConformalFactor_inverseUniformScaleConformalMap_eq
  {ι : Type*}
  [Fintype ι]
  {a : ι → Complex}
  {rho : Real}
-- given
  (hrho : 0 < rho) :
-- imply
  spinConformalFactor (inverseUniformScaleConformalMap rho) a = ∏ _ : ι, rho ^ (-isingSpinScalingDimension) := by
-- proof
  apply StatMech.FrontierA.spinConformalFactor_inverseUniformScaleConformalMap ι a hrho

/--
[tendsto_squareBoxRenormalizedSpinCorrelation_inverseUniformScale_of_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma tendsto_squareBoxRenormalizedSpinCorrelation_inverseUniformScale_of_relabel_eq
  {ι : Type*}
  [Fintype ι]
  {sourceδ targetδ : Nat → Real}
  {sourceRadius targetRadius : Nat → Nat}
  {a : ι → Complex}
  {rho L : Real}
-- given
  (hsourceδ : ∀ n, 0 < sourceδ n)
  (htargetδ : ∀ n, 0 < targetδ n)
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
  (hσ : ∀ n x y, (boxGraph 2 (sourceRadius n)).Adj x y ↔ (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
  (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i)
  (hrho : 0 < rho)
  (hratio : Tendsto (fun n ↦ targetδ n / sourceδ n) atTop (nhds rho))
  (hsource : Tendsto (squareBoxRenormalizedSpinCorrelation ι sourceδ β h sourceRadius sourceMarked) atTop (nhds L)) :
-- imply
  Tendsto (squareBoxRenormalizedSpinCorrelation ι targetδ β h targetRadius targetMarked) atTop (nhds (spinConformalFactor (inverseUniformScaleConformalMap rho) a * L)) := by
-- proof
  apply StatMech.FrontierA.tendsto_squareBoxRenormalizedSpinCorrelation_inverseUniformScale_of_relabel ι sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked a hrho hratio hsource

/--
[squareBox_radius_eq_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma squareBox_radius_eq_of_equiv_eq
  {sourceRadius targetRadius : Nat}
  {σ : boxVerts 2 sourceRadius ≃ boxVerts 2 targetRadius} :
-- imply
  sourceRadius = targetRadius := by
-- proof
  apply StatMech.FrontierA.squareBox_radius_eq_of_equiv σ

/--
[squareBox_radiusSequence_eq_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma squareBox_radiusSequence_eq_of_equiv_eq
  {sourceRadius targetRadius : Nat → Nat}
-- given
  (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n)) :
-- imply
  sourceRadius = targetRadius := by
-- proof
  apply StatMech.FrontierA.squareBox_radiusSequence_eq_of_equiv σ

/--
[squareBoxRenormalizedSpinCorrelation_eq_of_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma squareBoxRenormalizedSpinCorrelation_eq_of_relabel_eq
  {ι : Type*}
  [Fintype ι]
  {δ : Nat → Real}
  {sourceRadius targetRadius : Nat → Nat}
-- given
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
  (hσ : ∀ n x y, (boxGraph 2 (sourceRadius n)).Adj x y ↔ (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
  (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) :
-- imply
  squareBoxRenormalizedSpinCorrelation ι δ β h sourceRadius sourceMarked = squareBoxRenormalizedSpinCorrelation ι δ β h targetRadius targetMarked := by
-- proof
  apply StatMech.FrontierA.squareBoxRenormalizedSpinCorrelation_eq_of_relabel ι δ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked

/--
[squareBoxRenormalizedSpinCorrelation_transportError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean)
-/
@[path]
private lemma squareBoxRenormalizedSpinCorrelation_transportError_eq_zero_eq
  {ι : Type*}
  [Fintype ι]
  {δ : Nat → Real}
  {sourceRadius targetRadius : Nat → Nat}
  {n : Nat}
-- given
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
  (hσ : ∀ n x y, (boxGraph 2 (sourceRadius n)).Adj x y ↔ (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
  (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) :
-- imply
  squareBoxRenormalizedSpinCorrelation ι δ β h targetRadius targetMarked n - squareBoxRenormalizedSpinCorrelation ι δ β h sourceRadius sourceMarked n = 0 := by
-- proof
  apply StatMech.FrontierA.squareBoxRenormalizedSpinCorrelation_transportError_eq_zero ι δ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked n


-- created on 2026-10-23
