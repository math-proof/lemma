import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[stac_removeSites_no_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_removeSites_no_neighbor_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x w : Site d}
-- given
  (hxT : x ∈ T) :
-- imply
  ¬ (openSubgraph d (removeSites T ω)).Adj x w := by
-- proof
  apply StatMech.Percolation.stac_removeSites_no_neighbor T ω hxT

/--
[stac_removeSites_connected_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_removeSites_connected_eq_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x v : Site d}
-- given
  (hxT : x ∈ T)
  (hconn : Connected d (removeSites T ω) x v) :
-- imply
  v = x := by
-- proof
  apply StatMech.Percolation.stac_removeSites_connected_eq T ω hxT hconn

/--
[stac_removeSites_cluster_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_removeSites_cluster_singleton_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hxT : x ∈ T) :
-- imply
  cluster d (removeSites T ω) x = {x} := by
-- proof
  apply StatMech.Percolation.stac_removeSites_cluster_singleton T ω hxT

/--
[stac_infiniteCluster_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_infiniteCluster_notMem_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : Site d}
-- given
  (hinf : (cluster d (removeSites T ω) w).Infinite) :
-- imply
  w ∉ T := by
-- proof
  apply StatMech.Percolation.stac_infiniteCluster_notMem T ω hinf

/--
[stac_sameArm_of_sameClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_sameArm_of_sameClass_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₀ aj u v : Site d}
-- given
  (hxu : Connected d ω x₀ u)
  (hneu : x₀ ≠ u)
  (hxv : Connected d ω x₀ v)
  (hnev : x₀ ≠ v)
  (hu : Connected d (removeSite x₀ ω) aj u)
  (hv : Connected d (removeSite x₀ ω) aj v) :
-- imply
  fsp_sameArm ω x₀ u v := by
-- proof
  apply StatMech.Percolation.stac_sameArm_of_sameClass ω hxu hneu hxv hnev hu hv

/--
[stac_claw_unsat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_claw_unsat_eq
  {d : ℕ}
  {cx : Fin 3}
  {cy : Fin 3 → Fin 3}
  {ay : Fin 3 → Fin 3}
  {ayj : Fin 3 → Fin 3 → Fin 3}
-- given
  (Gay : ∀ i, ay i = 0 ↔ cy i ≠ i)
  (Gayj : ∀ i j, ayj i j = 0 ↔ cy j ≠ i)
  (Dx0 : ∀ i, cx ≠ cy i)
  (Dyiyj : ∀ i j, j ≠ i → ay i ≠ ayj i j) :
-- imply
  False := by
-- proof
  apply StatMech.Percolation.stac_claw_unsat cx cy ay ayj Gay Gayj Dx0 Dyiyj

/--
[stac_claw_shadow_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_claw_shadow_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (cy : Fin 3 → Fin 3) (ay : Fin 3 → Fin 3) (ayj : Fin 3 → Fin 3 → Fin 3), (∀ i, ay i = 0 ↔ cy i ≠ i) ∧ (∀ i j, ayj i j = 0 ↔ cy j ≠ i) := by
-- proof
  apply StatMech.Percolation.stac_claw_shadow_consistent

/--
[stac_colorOf_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_colorOf_faithful_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₀ : Site d}
  {a : Fin 3 → Site d}
  {u v : Site d}
-- given
  (hsep : ∀ i j, i ≠ j → ¬ Connected d (removeSite x₀ ω) (a i) (a j))
  (hcover : ∀ w, Connected d ω x₀ w → x₀ ≠ w → ∃ i, Connected d (removeSite x₀ ω) (a i) (fsp_armWitness ω x₀ w))
  (hu : Connected d ω x₀ u)
  (hneu : x₀ ≠ u)
  (hv : Connected d ω x₀ v)
  (hnev : x₀ ≠ v) :
-- imply
  stac_colorOf ω x₀ a u = stac_colorOf ω x₀ a v ↔ fsp_sameArm ω x₀ u v := by
-- proof
  apply StatMech.Percolation.stac_colorOf_faithful ω x₀ a hsep hcover hu hneu hv hnev

/--
[stac_not_divergentArmOrder_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_not_divergentArmOrder_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : stac_ClawConfig ω n) :
-- imply
  ¬ fsp_DivergentArmOrder ω n := by
-- proof
  apply StatMech.Percolation.stac_not_divergentArmOrder_of_claw ω n hclaw

/--
[stac_claw_excludes_divergentArmOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_claw_excludes_divergentArmOrder_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : stac_ClawConfig ω n)
  (hdiv : fsp_DivergentArmOrder ω n) :
-- imply
  False := by
-- proof
  apply StatMech.Percolation.stac_claw_excludes_divergentArmOrder ω n hclaw hdiv

/--
[stac_uniform_divergentArmOrder_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean)
-/
@[path]
private lemma stac_uniform_divergentArmOrder_false_eq
  {d : ℕ}
-- given
  (hex : ∃ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n ∧ stac_ClawConfig ω n) :
-- imply
  ¬ (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_DivergentArmOrder ω n) := by
-- proof
  apply StatMech.Percolation.stac_uniform_divergentArmOrder_false hex


-- created on 2026-10-23
