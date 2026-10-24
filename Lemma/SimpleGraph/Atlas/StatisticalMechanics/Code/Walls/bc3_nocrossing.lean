import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc3_nocrossing
open Set StatMech.Lattice StatMech StatMech.Walls


/--
[bc3_connected_of_openEdge_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_nocrossing.lean)
-/
@[path]
private lemma bc3_connected_of_openEdge_between_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y u v : Site d}
-- given
  (hxu : Connected d ω x u)
  (hvy : Connected d ω y v)
  (huv : IsOpenEdge d ω u v) :
-- imply
  Connected d ω x y := by
-- proof
  apply StatMech.Walls.bc3_connected_of_openEdge_between hxu hvy huv

/--
[bc3_clusters_eq_of_openEdge_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_nocrossing.lean)
-/
@[path]
private lemma bc3_clusters_eq_of_openEdge_between_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y u v : Site d}
-- given
  (hxu : Connected d ω x u)
  (hvy : Connected d ω y v)
  (huv : IsOpenEdge d ω u v) :
-- imply
  cluster d ω x = cluster d ω y := by
-- proof
  apply StatMech.Walls.bc3_clusters_eq_of_openEdge_between hxu hvy huv

/--
[bc3_no_crossing_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_nocrossing.lean)
-/
@[path]
private lemma bc3_no_crossing_pair_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y u v : Site d}
-- given
  (hu : u ∈ cluster d ω x)
  (hv : v ∈ cluster d ω y)
  (huv : IsOpenEdge d ω u v) :
-- imply
  cluster d ω x = cluster d ω y := by
-- proof
  apply StatMech.Walls.bc3_no_crossing_pair hu hv huv

/--
[bc3_no_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_nocrossing.lean)
-/
@[path]
private lemma bc3_no_crossing_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hne : cluster d ω x ≠ cluster d ω y) :
-- imply
  ∀ ⦃u : Site d⦄, u ∈ cluster d ω x → ∀ ⦃v : Site d⦄, v ∈ cluster d ω y → ¬ IsOpenEdge d ω u v := by
-- proof
  apply StatMech.Walls.bc3_no_crossing hne


-- created on 2026-10-23
