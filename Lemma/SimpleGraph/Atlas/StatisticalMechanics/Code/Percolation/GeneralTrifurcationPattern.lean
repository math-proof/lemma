import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.GeneralTrifurcationPattern
open Set SimpleGraph Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[exteriorOpenGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GeneralTrifurcationPattern.lean)
-/
@[path]
private lemma exteriorOpenGraph_le_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  exteriorOpenGraph omega n ≤ openSubgraph d omega := by
-- proof
  apply StatMech.Percolation.exteriorOpenGraph_le omega n

/--
[three_infinite_clusters_finite_pattern_canonical_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GeneralTrifurcationPattern.lean)
-/
@[path]
private lemma three_infinite_clusters_finite_pattern_canonical_trifurcation_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Fin 3 → Site d}
-- given
  (hx : ∀ i, x i ∈ box d n)
  (hinf : ∀ i, (cluster d omega (x i)).Infinite)
  (hclusters : ∀ i j, i ≠ j → cluster d omega (x i) ≠ cluster d omega (x j)) :
-- imply
  ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n)) (hub : Site d), IsCanonicalTrifurcation d (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta omega) hub := by
-- proof
  apply StatMech.Percolation.three_infinite_clusters_finite_pattern_canonical_trifurcation omega n x hx hinf hclusters

/--
[three_infinite_clusters_finite_pattern_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GeneralTrifurcationPattern.lean)
-/
@[path]
private lemma three_infinite_clusters_finite_pattern_trifurcation_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Fin 3 → Site d}
-- given
  (hx : ∀ i, x i ∈ box d n)
  (hinf : ∀ i, (cluster d omega (x i)).Infinite)
  (hclusters : ∀ i j, i ≠ j → cluster d omega (x i) ≠ cluster d omega (x j)) :
-- imply
  ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n)) (hub : Site d), IsTrifurcation d (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta omega) hub := by
-- proof
  apply StatMech.Percolation.three_infinite_clusters_finite_pattern_trifurcation omega n x hx hinf hclusters

/--
[three_sites_finite_pattern_canonical_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GeneralTrifurcationPattern.lean)
-/
@[path]
private lemma three_sites_finite_pattern_canonical_trifurcation_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a b c : Site d}
-- given
  (ha : a ∈ box d n)
  (hb : b ∈ box d n)
  (hc : c ∈ box d n)
  (hia : (cluster d omega a).Infinite)
  (hib : (cluster d omega b).Infinite)
  (hic : (cluster d omega c).Infinite)
  (hab : cluster d omega a ≠ cluster d omega b)
  (hac : cluster d omega a ≠ cluster d omega c)
  (hbc : cluster d omega b ≠ cluster d omega c) :
-- imply
  ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n)) (hub : Site d), IsCanonicalTrifurcation d (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta omega) hub := by
-- proof
  apply StatMech.Percolation.three_sites_finite_pattern_canonical_trifurcation omega n a b c ha hb hc hia hib hic hab hac hbc

/--
[three_sites_finite_pattern_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GeneralTrifurcationPattern.lean)
-/
@[path]
private lemma three_sites_finite_pattern_trifurcation_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a b c : Site d}
-- given
  (ha : a ∈ box d n)
  (hb : b ∈ box d n)
  (hc : c ∈ box d n)
  (hia : (cluster d omega a).Infinite)
  (hib : (cluster d omega b).Infinite)
  (hic : (cluster d omega c).Infinite)
  (hab : cluster d omega a ≠ cluster d omega b)
  (hac : cluster d omega a ≠ cluster d omega c)
  (hbc : cluster d omega b ≠ cluster d omega c) :
-- imply
  ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n)) (hub : Site d), IsTrifurcation d (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta omega) hub := by
-- proof
  apply StatMech.Percolation.three_sites_finite_pattern_trifurcation omega n a b c ha hb hc hia hib hic hab hac hbc


-- created on 2026-10-23
