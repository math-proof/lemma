import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.G3PercDefs.Part9
open MeasureTheory Set StatMech StatMech.Universality


/--
[g3OriginCluster_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma g3OriginCluster_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  g3OriginCluster d ω = originCluster d ω := by
-- proof
  apply StatMech.Universality.g3OriginCluster_eq ω

/--
[origin_mem_g3OriginCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma origin_mem_g3OriginCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  (0 : Site d) ∈ g3OriginCluster d ω := by
-- proof
  apply StatMech.Universality.origin_mem_g3OriginCluster ω

/--
[g3OriginCluster_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma g3OriginCluster_mono_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ω ≤ ω') :
-- imply
  g3OriginCluster d ω ⊆ g3OriginCluster d ω' := by
-- proof
  apply StatMech.Universality.g3OriginCluster_mono h

/--
[g3PercolationEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma g3PercolationEvent_eq_eq
  {d : ℕ} :
-- imply
  g3PercolationEvent d = percolationEvent d := by
-- proof
  apply StatMech.Universality.g3PercolationEvent_eq

/--
[mem_g3PercolationEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma mem_g3PercolationEvent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ g3PercolationEvent d ↔ (g3OriginCluster d ω).Infinite := by
-- proof
  apply StatMech.Universality.mem_g3PercolationEvent

/--
[g3PercolationEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma g3PercolationEvent_increasing_eq
  {d : ℕ} :
-- imply
  IsIncreasing (g3PercolationEvent d) := by
-- proof
  apply StatMech.Universality.g3PercolationEvent_increasing

/--
[g3PercolationProbability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma g3PercolationProbability_eq_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  g3PercolationProbability d p hp = percolationProbability d p hp := by
-- proof
  apply StatMech.Universality.g3PercolationProbability_eq d p hp

/--
[g3SubcriticalDensities_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma g3SubcriticalDensities_eq_eq
  {d : ℕ} :
-- imply
  g3SubcriticalDensities d = subcriticalDensities d := by
-- proof
  apply StatMech.Universality.g3SubcriticalDensities_eq

/--
[g3CriticalProbability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma g3CriticalProbability_eq_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  g3CriticalProbability d = criticalProbability d := by
-- proof
  apply StatMech.Universality.g3CriticalProbability_eq d

/--
[G3PositivelyAssociated_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma G3PositivelyAssociated_iff_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace E)} :
-- imply
  G3PositivelyAssociated μ ↔ PositivelyAssociated μ := by
-- proof
  apply StatMech.Universality.G3PositivelyAssociated_iff μ

/--
[G3PositivelyAssociated.symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma symm_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace E)}
  {A B : Set (ConfigSpace E)}
-- given
  (h : G3PositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  μ.real B * μ.real A ≤ μ.real (B ∩ A) := by
-- proof
  apply StatMech.Universality.G3PositivelyAssociated.symm h A B hA hB

/--
[G3PositivelyAssociated.sq_le_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma sq_le_self_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (h : G3PositivelyAssociated μ)
  (hA : IsIncreasing A) :
-- imply
  μ.real A * μ.real A ≤ μ.real A := by
-- proof
  apply StatMech.Universality.G3PositivelyAssociated.sq_le_self h A hA

/--
[bernoulli_g3PositivelyAssociated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma bernoulli_g3PositivelyAssociated_eq
  {d : ℕ}
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
-- given
  (hp : p ≤ 1) :
-- imply
  G3PositivelyAssociated (bernoulliProductMeasure (E := E) p hp) := by
-- proof
  apply StatMech.Universality.bernoulli_g3PositivelyAssociated hp

/--
[g3BoxCrossingProbabilities_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma g3BoxCrossingProbabilities_eq_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
  {n0 : ℕ} :
-- imply
  g3BoxCrossingProbabilities μ ρ n0 = boxCrossingProbabilities μ ρ n0 := by
-- proof
  apply StatMech.Universality.g3BoxCrossingProbabilities_eq μ ρ n0

/--
[g3BoxCrossingInf_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma g3BoxCrossingInf_eq_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
  {n0 : ℕ} :
-- imply
  g3BoxCrossingInf μ ρ n0 = sInf (g3BoxCrossingProbabilities μ ρ n0) := by
-- proof
  apply StatMech.Universality.g3BoxCrossingInf_eq μ ρ n0

/--
[G3BoxCrossingProperty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma G3BoxCrossingProperty_iff_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ} :
-- imply
  G3BoxCrossingProperty μ ρ ↔ BoxCrossingProperty μ ρ := by
-- proof
  apply StatMech.Universality.G3BoxCrossingProperty_iff μ ρ

/--
[G3BoxCrossingProperty.one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma one_lt_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
-- given
  (h : G3BoxCrossingProperty μ ρ) :
-- imply
  1 < ρ := by
-- proof
  apply StatMech.Universality.G3BoxCrossingProperty.one_lt h

/--
[G3BoxCrossingProperty.exists_pos_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean)
-/
@[path]
private lemma exists_pos_inf_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
-- given
  (h : G3BoxCrossingProperty μ ρ) :
-- imply
  ∃ n0 : ℕ, 0 < g3BoxCrossingInf μ ρ n0 := by
-- proof
  apply StatMech.Universality.G3BoxCrossingProperty.exists_pos_inf h


-- created on 2026-10-23
