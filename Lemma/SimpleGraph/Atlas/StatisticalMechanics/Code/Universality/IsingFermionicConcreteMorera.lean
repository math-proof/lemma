import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicConcreteMorera
open StatMech StatMech.Universality


/--
[fkIsingExpandingBoundarySquare_orderedRectangleContour_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConcreteMorera.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_orderedRectangleContour_eq_zero_eq
  {sigma : Nat -> Nat}
  {f : Complex -> Complex}
  {z w : Complex}
-- given
  (hsigma : Tendsto sigma atTop atTop)
  (hlimit : TendstoLocallyUniformlyOn (fun r => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant (sigma r)) f atTop Set.univ)
  (hre : z.re ≤ w.re)
  (him : z.im ≤ w.im) :
-- imply
  Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f = 0 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_orderedRectangleContour_eq_zero hsigma hlimit z w hre him

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_isConservativeOn_subsequentialLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConcreteMorera.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_isConservativeOn_subsequentialLimit_eq
  {sigma : Nat -> Nat}
  {f : Complex -> Complex}
-- given
  (hsigma : Tendsto sigma atTop atTop)
  (hlimit : TendstoLocallyUniformlyOn (fun r => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant (sigma r)) f atTop Set.univ) :
-- imply
  Complex.IsConservativeOn f Set.univ := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_isConservativeOn_subsequentialLimit hsigma hlimit

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_differentiable_subsequentialLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicConcreteMorera.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_differentiable_subsequentialLimit_eq
  {sigma : Nat -> Nat}
  {f : Complex -> Complex}
-- given
  (hsigma : Tendsto sigma atTop atTop)
  (hlimit : TendstoLocallyUniformlyOn (fun r => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant (sigma r)) f atTop Set.univ) :
-- imply
  Differentiable Complex f := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_differentiable_subsequentialLimit hsigma hlimit


-- created on 2026-10-23
