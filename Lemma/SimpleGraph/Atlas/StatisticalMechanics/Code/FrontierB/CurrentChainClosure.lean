import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentChainClosure
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[plusFreeSuperposedTraceLaw_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentChainClosure.lean)
-/
@[path]
private lemma plusFreeSuperposedTraceLaw_uniqueness_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 <= beta)
  (hd : 1 <= d) :
-- imply
  let mu := (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta) (infiniteFreeCurrentMeasure d beta hbeta) : Measure (ConfigSpace (Sym2 (Site d)))) (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨ mu {omega | numInfiniteClusters d omega = 1} = 1) ∧ mu (atLeastTwoInfinite d) = 0 ∧ mu {omega | numInfiniteClusters d omega <= 1} = 1 := by
-- proof
  apply StatMech.FrontierB.plusFreeSuperposedTraceLaw_uniqueness d beta hbeta hd

/--
[infinitePlusFreeSource_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentChainClosure.lean)
-/
@[path]
private lemma infinitePlusFreeSource_switching_eq
  {d N : Nat}
  {beta : Real}
  {x y : Site d}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 1 <= d)
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y)
  (hQ : IsClopen Q) :
-- imply
  ((∫ omega, spinProd ({x, y} : Finset (Site d)) omega ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) * (∫ omega, spinProd ({x, y} : Finset (Site d)) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) * (((infinitePlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy).prod (infiniteFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) : Measure _).real (superposedCurrentTrace ⁻¹' Q)) = (((infinitePlusCurrentMeasure d beta hbeta.le).prod (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real (currentPairTraceConnectionGate Q x y)) := by
-- proof
  apply StatMech.FrontierB.infinitePlusFreeSource_switching d N hd beta hbeta x y hx hy hxy Q hQ

/--
[currentContinuityMixedTraceLaw_genMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentChainClosure.lean)
-/
@[path]
private lemma currentContinuityMixedTraceLaw_genMixing_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 <= d)
  (hbeta : 0 < beta) :
-- imply
  fmu_GenMixing (G := Multiplicative (Site d)) (currentContinuityMixedTraceLaw d beta hbeta : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.currentContinuityMixedTraceLaw_genMixing d hd beta hbeta

/--
[currentContinuityMixedTraceLaw_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentChainClosure.lean)
-/
@[path]
private lemma currentContinuityMixedTraceLaw_isTranslationInvariant_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  IsTranslationInvariant (G := Multiplicative (Site d)) (currentContinuityMixedTraceLaw d beta hbeta : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.currentContinuityMixedTraceLaw_isTranslationInvariant d beta hbeta

/--
[currentContinuityMixedTraceLaw_uniqueInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentChainClosure.lean)
-/
@[path]
private lemma currentContinuityMixedTraceLaw_uniqueInfiniteCluster_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 <= d)
  (hbeta : 0 < beta) :
-- imply
  (currentContinuityMixedTraceLaw d beta hbeta : Measure _) (atLeastTwoInfinite d) = 0 := by
-- proof
  apply StatMech.FrontierB.currentContinuityMixedTraceLaw_uniqueInfiniteCluster d hd beta hbeta

/--
[currentContinuityMixedTraceLaw_percolationPrinciple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentChainClosure.lean)
-/
@[path]
private lemma currentContinuityMixedTraceLaw_percolationPrinciple_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 <= d)
  (hbeta : 0 < beta) :
-- imply
  CurrentContinuityPercolationPrinciple d (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
-- proof
  apply StatMech.FrontierB.currentContinuityMixedTraceLaw_percolationPrinciple d hd beta hbeta


-- created on 2026-10-23
