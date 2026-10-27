import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalCycleCover.Part2
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[summable_ons_rectDualPathCriticalCycleCoverTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalCycleCover.lean)
-/
@[path]
private lemma summable_ons_rectDualPathCriticalCycleCoverTerm_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N} :
-- imply
  Summable (ons_rectDualPathCriticalCycleCoverTerm embedding path) := by
-- proof
  apply StatMech.Onsager.summable_ons_rectDualPathCriticalCycleCoverTerm embedding path

/--
[tsum_ons_rectDualPathCriticalCycleCoverTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalCycleCover.lean)
-/
@[path]
private lemma tsum_ons_rectDualPathCriticalCycleCoverTerm_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N} :
-- imply
  ∑' sigma, ons_rectDualPathCriticalCycleCoverTerm embedding path sigma = (ons_sourceX (ons_rectDualGraph M N) {path.source, path.target} ons_signedLoopCriticalWeight : Complex) ^ 2 := by
-- proof
  apply StatMech.Onsager.tsum_ons_rectDualPathCriticalCycleCoverTerm embedding path

/--
[summable_ons_rectDualPathCriticalNormalizedCycleCoverTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalCycleCover.lean)
-/
@[path]
private lemma summable_ons_rectDualPathCriticalNormalizedCycleCoverTerm_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N} :
-- imply
  Summable (ons_rectDualPathCriticalNormalizedCycleCoverTerm embedding path) := by
-- proof
  apply StatMech.Onsager.summable_ons_rectDualPathCriticalNormalizedCycleCoverTerm embedding path

/--
[tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalCycleCover.lean)
-/
@[path]
private lemma tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N} :
-- imply
  ∑' sigma, ons_rectDualPathCriticalNormalizedCycleCoverTerm embedding path sigma = (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) ons_betaC 0 (fun config => StatMech.Ising.spin config path.source * StatMech.Ising.spin config path.target) : Complex) ^ 2 := by
-- proof
  apply StatMech.Onsager.tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm embedding path

/--
[norm_tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalCycleCover.lean)
-/
@[path]
private lemma norm_tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm_le_one_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N} :
-- imply
  ‖∑' sigma, ons_rectDualPathCriticalNormalizedCycleCoverTerm embedding path sigma‖ ≤ 1 := by
-- proof
  apply StatMech.Onsager.norm_tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm_le_one embedding path

/--
[ons_rectDualPathCriticalNormalizedCycleCover_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalCycleCover.lean)
-/
@[path]
private lemma ons_rectDualPathCriticalNormalizedCycleCover_tendsto_freeState_eq
  {a b : StatMech.Lattice.Site 2}
-- given
  (embedding : ∀ n, KWStraightLineEmbedding (ons_rectDualGraph (2 * n) (2 * n)))
  (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
  (hsource : ∀ᶠ n in Filter.atTop, ((ons_box2EquivRect n).symm (path n).source).1 = a)
  (htarget : ∀ᶠ n in Filter.atTop, ((ons_box2EquivRect n).symm (path n).target).1 = b) :
-- imply
  Filter.Tendsto (fun n => ∑' sigma, ons_rectDualPathCriticalNormalizedCycleCoverTerm (embedding n) (path n) sigma) Filter.atTop (nhds ((((∫ spin, StatMech.Ising.spinProd {a, b} spin ∂(StatMech.Ising.freeState 2 ons_betaC 0 : MeasureTheory.Measure (StatMech.ConfigSpace (StatMech.Lattice.Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_rectDualPathCriticalNormalizedCycleCover_tendsto_freeState embedding path a b hsource htarget


-- created on 2026-10-23
