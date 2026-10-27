import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinAffineSimilarityTransport.Part2
open Filter Topology StatMech StatMech.FrontierA


/--
[squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinAffineSimilarityTransport.lean)
-/
@[path]
private lemma squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel_eq
  {ι : Type*}
  [Fintype ι]
  {reindex : Nat → Nat}
  {sourceδ targetδ : Nat → Real}
  {sourceRadius targetRadius : Nat → Nat}
  {n : Nat}
-- given
  (hsourceδ : ∀ n, 0 < sourceδ n)
  (htargetδ : ∀ n, 0 < targetδ n)
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (σ : ∀ n, boxVerts 2 (sourceRadius (reindex n)) ≃ boxVerts 2 (targetRadius n))
  (hσ : ∀ n x y, (boxGraph 2 (sourceRadius (reindex n))).Adj x y ↔ (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
  (hmarked : ∀ n i, σ n (sourceMarked (reindex n) i) = targetMarked n i) :
-- imply
  squareBoxRenormalizedSpinCorrelation ι targetδ β h targetRadius targetMarked n = (∏ _ : ι, (targetδ n / sourceδ (reindex n)) ^ (-isingSpinScalingDimension)) * squareBoxRenormalizedSpinCorrelation ι sourceδ β h sourceRadius sourceMarked (reindex n) := by
-- proof
  apply StatMech.FrontierA.squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel ι reindex sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked n

/--
[tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinAffineSimilarityTransport.lean)
-/
@[path]
private lemma tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel_eq
  {ι : Type*}
  [Fintype ι]
  {reindex : Nat → Nat}
  {sourceδ targetδ : Nat → Real}
  {sourceRadius targetRadius : Nat → Nat}
  {ρ L : Real}
-- given
  (hreindex : Tendsto reindex atTop atTop)
  (hsourceδ : ∀ n, 0 < sourceδ n)
  (htargetδ : ∀ n, 0 < targetδ n)
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (σ : ∀ n, boxVerts 2 (sourceRadius (reindex n)) ≃ boxVerts 2 (targetRadius n))
  (hσ : ∀ n x y, (boxGraph 2 (sourceRadius (reindex n))).Adj x y ↔ (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
  (hmarked : ∀ n i, σ n (sourceMarked (reindex n) i) = targetMarked n i)
  (hρ : 0 < ρ)
  (hratio : Tendsto (fun n ↦ targetδ n / sourceδ (reindex n)) atTop (nhds ρ))
  (hsource : Tendsto (squareBoxRenormalizedSpinCorrelation ι sourceδ β h sourceRadius sourceMarked) atTop (nhds L)) :
-- imply
  Tendsto (squareBoxRenormalizedSpinCorrelation ι targetδ β h targetRadius targetMarked) atTop (nhds ((∏ _ : ι, ρ ^ (-isingSpinScalingDimension)) * L)) := by
-- proof
  apply StatMech.FrontierA.tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel ι reindex hreindex sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked hρ hratio hsource

/--
[deriv_inverseUniformScaleAffineConformalMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinAffineSimilarityTransport.lean)
-/
@[path]
private lemma deriv_inverseUniformScaleAffineConformalMap_eq
  {ρ : Real}
  {b z : Complex} :
-- imply
  deriv (inverseUniformScaleAffineConformalMap ρ b) z = (ρ⁻¹ : Complex) := by
-- proof
  apply StatMech.FrontierA.deriv_inverseUniformScaleAffineConformalMap ρ b z

/--
[spinConformalFactor_inverseUniformScaleAffineConformalMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinAffineSimilarityTransport.lean)
-/
@[path]
private lemma spinConformalFactor_inverseUniformScaleAffineConformalMap_eq
  {ι : Type*}
  [Fintype ι]
  {a : ι → Complex}
  {b : Complex}
  {ρ : Real}
-- given
  (hρ : 0 < ρ) :
-- imply
  spinConformalFactor (inverseUniformScaleAffineConformalMap ρ b) a = ∏ _ : ι, ρ ^ (-isingSpinScalingDimension) := by
-- proof
  apply StatMech.FrontierA.spinConformalFactor_inverseUniformScaleAffineConformalMap ι a b hρ

/--
[tendsto_squareBoxRenormalizedSpinCorrelation_affine_of_reindexed_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinAffineSimilarityTransport.lean)
-/
@[path]
private lemma tendsto_squareBoxRenormalizedSpinCorrelation_affine_of_reindexed_relabel_eq
  {ι : Type*}
  [Fintype ι]
  {reindex : Nat → Nat}
  {sourceδ targetδ : Nat → Real}
  {sourceRadius targetRadius : Nat → Nat}
  {a : ι → Complex}
  {b : Complex}
  {ρ L : Real}
-- given
  (hreindex : Tendsto reindex atTop atTop)
  (hsourceδ : ∀ n, 0 < sourceδ n)
  (htargetδ : ∀ n, 0 < targetδ n)
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
  (σ : ∀ n, boxVerts 2 (sourceRadius (reindex n)) ≃ boxVerts 2 (targetRadius n))
  (hσ : ∀ n x y, (boxGraph 2 (sourceRadius (reindex n))).Adj x y ↔ (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
  (hmarked : ∀ n i, σ n (sourceMarked (reindex n) i) = targetMarked n i)
  (hρ : 0 < ρ)
  (hratio : Tendsto (fun n ↦ targetδ n / sourceδ (reindex n)) atTop (nhds ρ))
  (hsource : Tendsto (squareBoxRenormalizedSpinCorrelation ι sourceδ β h sourceRadius sourceMarked) atTop (nhds L)) :
-- imply
  Tendsto (squareBoxRenormalizedSpinCorrelation ι targetδ β h targetRadius targetMarked) atTop (nhds (spinConformalFactor (inverseUniformScaleAffineConformalMap ρ b) a * L)) := by
-- proof
  apply StatMech.FrontierA.tendsto_squareBoxRenormalizedSpinCorrelation_affine_of_reindexed_relabel ι reindex hreindex sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked a b hρ hratio hsource

/--
[tendsto_squareBoxRenormalizedSpinCorrelation_affine_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinAffineSimilarityTransport.lean)
-/
@[path]
private lemma tendsto_squareBoxRenormalizedSpinCorrelation_affine_reindex_eq
  {ι : Type*}
  [Fintype ι]
  {reindex : Nat → Nat}
  {sourceδ targetδ : Nat → Real}
  {sourceRadius : Nat → Nat}
  {a : ι → Complex}
  {b : Complex}
  {ρ L : Real}
-- given
  (hreindex : Tendsto reindex atTop atTop)
  (hsourceδ : ∀ n, 0 < sourceδ n)
  (htargetδ : ∀ n, 0 < targetδ n)
  (β h : Real)
  (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
  (hρ : 0 < ρ)
  (hratio : Tendsto (fun n ↦ targetδ n / sourceδ (reindex n)) atTop (nhds ρ))
  (hsource : Tendsto (squareBoxRenormalizedSpinCorrelation ι sourceδ β h sourceRadius sourceMarked) atTop (nhds L)) :
-- imply
  Tendsto (squareBoxRenormalizedSpinCorrelation ι targetδ β h (sourceRadius ∘ reindex) (fun n ↦ sourceMarked (reindex n))) atTop (nhds (spinConformalFactor (inverseUniformScaleAffineConformalMap ρ b) a * L)) := by
-- proof
  apply StatMech.FrontierA.tendsto_squareBoxRenormalizedSpinCorrelation_affine_reindex ι reindex hreindex sourceδ targetδ hsourceδ htargetδ β h sourceRadius sourceMarked a b hρ hratio hsource


-- created on 2026-10-23
