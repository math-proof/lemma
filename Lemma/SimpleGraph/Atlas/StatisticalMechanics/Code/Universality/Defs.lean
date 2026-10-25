import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
open MeasureTheory Set StatMech StatMech.Universality


/--
[openSubgraph_mono_dim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma openSubgraph_mono_dim_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ω ≤ ω') :
-- imply
  openSubgraph d ω ≤ openSubgraph d ω' := by
-- proof
  apply StatMech.Universality.openSubgraph_mono_dim h

/--
[connected_mono_dim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma connected_mono_dim_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : ω ≤ ω')
  (hxy : Connected d ω x y) :
-- imply
  Connected d ω' x y := by
-- proof
  apply StatMech.Universality.connected_mono_dim h hxy

/--
[cluster_mono_dim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma cluster_mono_dim_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : ω ≤ ω') :
-- imply
  cluster d ω x ⊆ cluster d ω' x := by
-- proof
  apply StatMech.Universality.cluster_mono_dim h x

/--
[mem_originCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma mem_originCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d} :
-- imply
  y ∈ originCluster d ω ↔ Connected d ω (0 : Site d) y := by
-- proof
  apply StatMech.Universality.mem_originCluster

/--
[origin_mem_originCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma origin_mem_originCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  (0 : Site d) ∈ originCluster d ω := by
-- proof
  apply StatMech.Universality.origin_mem_originCluster ω

/--
[originCluster_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma originCluster_mono_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ω ≤ ω') :
-- imply
  originCluster d ω ⊆ originCluster d ω' := by
-- proof
  apply StatMech.Universality.originCluster_mono h

/--
[mem_percolationEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma mem_percolationEvent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ percolationEvent d ↔ (originCluster d ω).Infinite := by
-- proof
  apply StatMech.Universality.mem_percolationEvent

/--
[percolationEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma percolationEvent_increasing_eq
  {d : ℕ} :
-- imply
  IsIncreasing (percolationEvent d) := by
-- proof
  apply StatMech.Universality.percolationEvent_increasing

/--
[PositivelyAssociated.symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma symm_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace E)}
  {A B : Set (ConfigSpace E)}
-- given
  (h : PositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  μ.real B * μ.real A ≤ μ.real (B ∩ A) := by
-- proof
  apply StatMech.Universality.PositivelyAssociated.symm h A B hA hB

/--
[PositivelyAssociated.sq_le_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma sq_le_self_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (h : PositivelyAssociated μ)
  (hA : IsIncreasing A) :
-- imply
  μ.real A * μ.real A ≤ μ.real A := by
-- proof
  apply StatMech.Universality.PositivelyAssociated.sq_le_self h A hA

/--
[translateConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma translateConfig_apply_eq
  {d : ℕ}
  {v : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  translateConfig v ω e = ω (e.map (· + v)) := by
-- proof
  apply StatMech.Universality.translateConfig_apply v ω e

/--
[translateConfig_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma translateConfig_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  translateConfig (0 : Site 2) ω = ω := by
-- proof
  apply StatMech.Universality.translateConfig_zero ω

/--
[translatedHorizontalCrossingEvent_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma translatedHorizontalCrossingEvent_zero_eq
  {d : ℕ}
  {a b : ℤ} :
-- imply
  translatedHorizontalCrossingEvent (0 : Site 2) a b = horizontalCrossingEvent a b := by
-- proof
  apply StatMech.Universality.translatedHorizontalCrossingEvent_zero a b

/--
[translatedVerticalCrossingEvent_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma translatedVerticalCrossingEvent_zero_eq
  {d : ℕ}
  {a b : ℤ} :
-- imply
  translatedVerticalCrossingEvent (0 : Site 2) a b = verticalCrossingEvent a b := by
-- proof
  apply StatMech.Universality.translatedVerticalCrossingEvent_zero a b

/--
[boxCrossingProperty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean)
-/
@[path]
private lemma boxCrossingProperty_iff_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ} :
-- imply
  BoxCrossingProperty μ ρ ↔ 1 < ρ ∧ ∃ n0 : ℕ, 0 < sInf (boxCrossingProbabilities μ ρ n0) := by
-- proof
  apply StatMech.Universality.boxCrossingProperty_iff μ ρ


-- created on 2026-10-23
