import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
open MeasureTheory StatMech StatMech.FrontierA


/--
[siteToBond_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma siteToBond_mk_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {x y : Site d} :
-- imply
  siteToBond eta s(x, y) = (eta x && eta y) := by
-- proof
  apply StatMech.FrontierA.siteToBond_mk eta x y

/--
[siteOpenGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma siteOpenGraph_adj_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {x y : Site d} :
-- imply
  (siteOpenGraph eta).Adj x y ↔ (hypercubicLattice d).Adj x y ∧ eta x = true ∧ eta y = true := by
-- proof
  apply StatMech.FrontierA.siteOpenGraph_adj eta x y

/--
[openSubgraph_siteToBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma openSubgraph_siteToBond_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  openSubgraph d (siteToBond eta) = siteOpenGraph eta := by
-- proof
  apply StatMech.FrontierA.openSubgraph_siteToBond eta

/--
[connected_siteToBond_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma connected_siteToBond_iff_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {x y : Site d} :
-- imply
  Connected d (siteToBond eta) x y ↔ (siteOpenGraph eta).Reachable x y := by
-- proof
  apply StatMech.FrontierA.connected_siteToBond_iff eta x y

/--
[siteToBond_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma siteToBond_mono_eq
  {d : ℕ}
  {eta eta' : ConfigSpace (Site d)}
-- given
  (h : eta ≤ eta') :
-- imply
  siteToBond eta ≤ siteToBond eta' := by
-- proof
  apply StatMech.FrontierA.siteToBond_mono h

/--
[measurable_siteToBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma measurable_siteToBond_eq
  {d : ℕ} :
-- imply
  Measurable (siteToBond : ConfigSpace (Site d) → ConfigSpace (Sym2 (Site d))) := by
-- proof
  apply StatMech.FrontierA.measurable_siteToBond

/--
[siteToBond_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma siteToBond_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {eta : ConfigSpace (Site d)} :
-- imply
  siteToBond (shift g eta) = shift g (siteToBond eta) := by
-- proof
  apply StatMech.FrontierA.siteToBond_shift g eta

/--
[infiniteClusters_siteToBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma infiniteClusters_siteToBond_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  infiniteClusters d (siteToBond eta) = {C : Set (Site d) | C.Infinite ∧ ∃ x, C = {y | (siteOpenGraph eta).Reachable x y}} := by
-- proof
  apply StatMech.FrontierA.infiniteClusters_siteToBond eta

/--
[numInfiniteClusters_siteToBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma numInfiniteClusters_siteToBond_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  numInfiniteClusters d (siteToBond eta) = ({C : Set (Site d) | C.Infinite ∧ ∃ x, C = {y | (siteOpenGraph eta).Reachable x y}}).encard := by
-- proof
  apply StatMech.FrontierA.numInfiniteClusters_siteToBond eta

/--
[siteToBond_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma siteToBond_isTranslationInvariant_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Site d))}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  IsTranslationInvariant (G := Multiplicative (Site d)) (Measure.map siteToBond mu) := by
-- proof
  apply StatMech.FrontierA.siteToBond_isTranslationInvariant mu hinv

/--
[siteToBond_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteBond.lean)
-/
@[path]
private lemma siteToBond_isErgodic_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Site d))}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) mu) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (Measure.map siteToBond mu) := by
-- proof
  apply StatMech.FrontierA.siteToBond_isErgodic mu herg


-- created on 2026-10-23
