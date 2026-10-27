import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc6windingwitness
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc6_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6windingwitness.lean)
-/
@[path]
private lemma kc6_windingWitness_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c : Site 2, ∃ hc : IsExtremeCell K c, c ∈ K ∧ ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
-- proof
  apply StatMech.Walls.kc6_windingWitness K hK hne

/--
[kc6_exists_windingWitness_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6windingwitness.lean)
-/
@[path]
private lemma kc6_exists_windingWitness_dart_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ a : {e : Dart // IsBoundaryDart K e}, ∃ z₀ : Site 2, z₀ ∈ K ∧ ¬ Even (jec_rayCount z₀ (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.kc6_exists_windingWitness_dart K hK hne

/--
[kc6_windingWitness_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6windingwitness.lean)
-/
@[path]
private lemma kc6_windingWitness_mem_leftRegion_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c : Site 2, ∃ hc : IsExtremeCell K c, c ∈ K ∧ c ∈ jec_leftRegion (mpl_orbitLoop K (extremeBase K c hc)) := by
-- proof
  apply StatMech.Walls.kc6_windingWitness_mem_leftRegion K hK hne

/--
[kc6_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6windingwitness.lean)
-/
@[path]
private lemma kc6_unitCell_windingWitness_eq :
-- imply
  (![0, 0] : Site 2) ∈ unitCell ∧ ¬ Even (jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Walls.kc6_unitCell_windingWitness


-- created on 2026-10-23
