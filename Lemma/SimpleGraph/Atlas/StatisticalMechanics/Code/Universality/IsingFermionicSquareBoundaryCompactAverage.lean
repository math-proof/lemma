import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryCompactAverage
open StatMech StatMech.Universality


/--
[fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable_eq
  {k : Nat} :
-- imply
  Differentiable Complex (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k

/--
[fkIsingExpandingBoundarySquare_normalizedInterpolant_holomorphic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_normalizedInterpolant_holomorphic_eq :
-- imply
  ∀ k, DifferentiableOn Complex (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_normalizedInterpolant_holomorphic

/--
[fkIsingExpandingBoundarySquareRadialSupport_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadialSupport_nonempty_eq
  {k : Nat} :
-- imply
  (fkIsingExpandingBoundarySquareRadialSupport k).Nonempty := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadialSupport_nonempty k

/--
[fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageNormSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageNormSq_eq :
-- imply
  FKIsingCaratheodoryApproximation.HasEventualCompactAverageNormSq fkIsingExpandingBoundarySquareCaratheodoryApproximation fkIsingExpandingBoundarySquareRadialSupport := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageNormSq

/--
[fkIsingExpandingBoundarySquareRadialSupport_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadialSupport_mem_closedBall_eq
  {k : Nat}
  {a : fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k}
-- given
  (hk : 15 ≤ k)
  (ha : a ∈ fkIsingExpandingBoundarySquareRadialSupport k) :
-- imply
  dist (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k a) 0 ≤ 4 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadialSupport_mem_closedBall k a hk ha

/--
[fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactWindowDiameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactWindowDiameter_eq :
-- imply
  FKIsingCaratheodoryApproximation.HasEventualCompactWindowDiameter fkIsingExpandingBoundarySquareCaratheodoryApproximation fkIsingExpandingBoundarySquareRadialSupport := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactWindowDiameter

/--
[fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageEnergy_eq :
-- imply
  FKIsingCaratheodoryApproximation.HasEventualCompactAverageEnergy fkIsingExpandingBoundarySquareCaratheodoryApproximation fkIsingExpandingBoundarySquareRadialSupport := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageEnergy

/--
[fkIsingExpandingBoundarySquare_eventualMedialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_eventualMedialBounds_eq
  {I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation} :
-- imply
  ∀ K : Set Complex, IsCompact K → K ⊆ fkIsingExpandingBoundarySquareCaratheodoryApproximation.U → ∃ B : Real, ∀ᶠ k in atTop, ∀ e : fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k, (∃ z ∈ K, dist z (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k e) ≤ fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) → ‖@FKIsingDobrushinDomain.normalizedFermionicObservable (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) e‖ ≤ B := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_eventualMedialBounds I

/--
[fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_primitiveIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_primitiveIm_eq
  {I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hidentifyPrimitive : ∀ (phi psi : Nat → Nat) (f : Complex → Complex), StrictMono phi → StrictMono psi → TendstoLocallyUniformlyOn (fun k ↦ fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant (phi (psi k))) f atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U → ∃ (P : Complex → Complex) (C : Real), DifferentiableOn Complex P fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧ Set.EqOn (deriv P) (fun z ↦ f z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧ (∀ z ∈ fkIsingExpandingBoundarySquareCaratheodoryApproximation.U, (P z).im = (Phi z).im + C) ∧ f fkIsingExpandingBoundarySquareCaratheodoryApproximation.root = target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) :
-- imply
  TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧ TendstoLocallyUniformlyOn (deriv ∘ fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant) (deriv target) atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_primitiveIm I target Phi htarget htarget_ne hPhi hPhideriv E hidentifyPrimitive

/--
[fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveIm_eq
  {I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hidentifyDense : ∀ (phi psi : Nat → Nat) (f : Complex → Complex), StrictMono phi → StrictMono psi → TendstoLocallyUniformlyOn (fun k ↦ fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant (phi (psi k))) f atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U → ∃ (S : Set Complex) (C : Real), Dense S ∧ Set.EqOn (fun z ↦ (isingFermionicEntireSquarePrimitive f z).im) (fun z ↦ (Phi z).im + C) S ∧ f fkIsingExpandingBoundarySquareCaratheodoryApproximation.root = target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) :
-- imply
  TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧ TendstoLocallyUniformlyOn (deriv ∘ fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant) (deriv target) atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveIm I target Phi htarget htarget_ne hPhi hPhideriv E hidentifyDense


-- created on 2026-10-23
