import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability.Part3
open Set StatMech StatMech.FrontierA


/--
[siteOpenGraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma siteOpenGraph_mono_eq
  {d : ℕ}
  {eta eta' : ConfigSpace (Site d)}
-- given
  (h : eta ≤ eta') :
-- imply
  siteOpenGraph eta ≤ siteOpenGraph eta' := by
-- proof
  apply StatMech.FrontierA.siteOpenGraph_mono h

/--
[le_raiseField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma le_raiseField_eq
  {d : ℕ}
  {xi : NonnegativeField d}
  {x : Site d}
-- given
  (r : ℝ≥0) :
-- imply
  xi ≤ raiseField xi x r := by
-- proof
  apply StatMech.FrontierA.le_raiseField xi x r

/--
[site_eq_true_of_siteCluster_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma site_eq_true_of_siteCluster_infinite_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hinf : (siteCluster eta x).Infinite) :
-- imply
  eta x = true := by
-- proof
  apply StatMech.FrontierA.site_eq_true_of_siteCluster_infinite eta x hinf

/--
[siteCluster_raise_eq_of_infinite_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma siteCluster_raise_eq_of_infinite_of_not_mem_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {xi : NonnegativeField d}
  {x y : Site d}
-- given
  (r : ℝ≥0)
  (hinf : (siteCluster (T (raiseField xi x r)) y).Infinite)
  (hx : x ∉ siteCluster (T (raiseField xi x r)) y) :
-- imply
  siteCluster (T (raiseField xi x r)) y = siteCluster (T xi) y := by
-- proof
  apply StatMech.FrontierA.siteCluster_raise_eq_of_infinite_of_not_mem T xi x y r hinf hx

/--
[raiseFields_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma raiseFields_empty_eq
  {d : ℕ}
  {xi : NonnegativeField d}
-- given
  (r : Site d → ℝ≥0) :
-- imply
  raiseFields xi ∅ r = xi := by
-- proof
  apply StatMech.FrontierA.raiseFields_empty xi r

/--
[raiseFields_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma raiseFields_insert_eq
  {d : ℕ}
  {xi : NonnegativeField d}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (r : Site d → ℝ≥0)
  (hx : x ∉ S) :
-- imply
  raiseFields xi (insert x S) r = raiseField (raiseFields xi S r) x (r x) := by
-- proof
  apply StatMech.FrontierA.raiseFields_insert xi S r hx

/--
[le_raiseFields](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma le_raiseFields_eq
  {d : ℕ}
  {xi : NonnegativeField d}
  {S : Finset (Site d)}
-- given
  (r : Site d → ℝ≥0) :
-- imply
  xi ≤ raiseFields xi S r := by
-- proof
  apply StatMech.FrontierA.le_raiseFields xi S r

/--
[raiseFields_mono_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma raiseFields_mono_set_eq
  {d : ℕ}
  {xi : NonnegativeField d}
  {S U : Finset (Site d)}
-- given
  (hSU : S ⊆ U)
  (r : Site d → ℝ≥0) :
-- imply
  raiseFields xi S r ≤ raiseFields xi U r := by
-- proof
  apply StatMech.FrontierA.raiseFields_mono_set xi hSU r

/--
[siteCluster_raiseFields_eq_of_infinite_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma siteCluster_raiseFields_eq_of_infinite_of_avoids_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {xi : NonnegativeField d}
  {S : Finset (Site d)}
  {y : Site d}
-- given
  (r : Site d → ℝ≥0)
  (hinf : (siteCluster (T xi) y).Infinite)
  (havoid : ∀ x ∈ S, x ∉ siteCluster (T (raiseFields xi S r)) y) :
-- imply
  siteCluster (T (raiseFields xi S r)) y = siteCluster (T xi) y := by
-- proof
  apply StatMech.FrontierA.siteCluster_raiseFields_eq_of_infinite_of_avoids T xi S r y hinf havoid

/--
[raiseFields_zeroFields](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma raiseFields_zeroFields_eq
  {d : ℕ}
  {xi : NonnegativeField d}
  {S : Finset (Site d)} :
-- imply
  raiseFields (zeroFields xi S) S xi = xi := by
-- proof
  apply StatMech.FrontierA.raiseFields_zeroFields xi S

/--
[siteCluster_zeroFields_eq_of_infinite_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean)
-/
@[path]
private lemma siteCluster_zeroFields_eq_of_infinite_of_avoids_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {xi : NonnegativeField d}
  {S : Finset (Site d)}
  {y : Site d}
-- given
  (hinf : (siteCluster (T (zeroFields xi S)) y).Infinite)
  (havoid : ∀ x ∈ S, x ∉ siteCluster (T xi) y) :
-- imply
  siteCluster (T (zeroFields xi S)) y = siteCluster (T xi) y := by
-- proof
  apply StatMech.FrontierA.siteCluster_zeroFields_eq_of_infinite_of_avoids T xi S y hinf havoid


-- created on 2026-10-23
