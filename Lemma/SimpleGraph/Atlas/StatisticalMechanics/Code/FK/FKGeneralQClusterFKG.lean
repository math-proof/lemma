import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FKGeneralQClusterFKG
open MeasureTheory Set StatMech StatMech.FK


/--
[fkgq_freeInfiniteVolume_clusterInfinite_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQClusterFKG.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_clusterInfinite_fkg_eq
  {p q : Real}
  {x y : Site 2}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  let mu := (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))) mu.real (clusterInfiniteEvent 2 x) * mu.real (clusterInfiniteEvent 2 y) <= mu.real (clusterInfiniteEvent 2 x ∩ clusterInfiniteEvent 2 y) := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_clusterInfinite_fkg hp hp1 hq x y


-- created on 2026-10-23
