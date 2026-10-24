import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample
open Finset StatMech StatMech.Ising


/--
[lpReplicaSameProfileCounter_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSameProfileCounterexample.lean)
-/
@[path]
private lemma lpReplicaSameProfileCounter_sources_eq :
-- imply
  StatMech.Sharpness.RandomCurrent.sources lpReplicaSameProfileCounterEnds Finset.univ = lpReplicaSameProfileCounterSi ∆ lpReplicaSameProfileCounterSj ∆ lpReplicaSameProfileCounterT := by
-- proof
  apply StatMech.Ising.lpReplicaSameProfileCounter_sources

/--
[lpReplicaSameProfileCounter_ghost_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSameProfileCounterexample.lean)
-/
@[path]
private lemma lpReplicaSameProfileCounter_ghost_disconn_eq :
-- imply
  ¬ connK lpReplicaSameProfileCounterEnds Finset.univ 0 1 := by
-- proof
  apply StatMech.Ising.lpReplicaSameProfileCounter_ghost_disconn

/--
[lpReplicaSameProfileCounter_no_target_selector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSameProfileCounterexample.lean)
-/
@[path]
private lemma lpReplicaSameProfileCounter_no_target_selector_eq :
-- imply
  ¬ ((∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧ StatMech.Sharpness.RandomCurrent.sources lpReplicaSameProfileCounterEnds P = lpReplicaSameProfileCounterSj ∆ lpReplicaSameProfileCounterT) ∨ (∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧ StatMech.Sharpness.RandomCurrent.sources lpReplicaSameProfileCounterEnds P = lpReplicaSameProfileCounterSi ∆ lpReplicaSameProfileCounterT)) := by
-- proof
  apply StatMech.Ising.lpReplicaSameProfileCounter_no_target_selector

/--
[exists_lpReplica_sameProfile_targetSelector_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSameProfileCounterexample.lean)
-/
@[path]
private lemma exists_lpReplica_sameProfile_targetSelector_counterexample_eq :
-- imply
  ∃ (ends : Fin 5 -> Sym2 (Fin 8)) (Si Sj T : Finset (Fin 8)), StatMech.Sharpness.RandomCurrent.sources ends Finset.univ = Si ∆ Sj ∆ T ∧ ¬ connK ends Finset.univ 0 1 ∧ ¬ ((∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧ StatMech.Sharpness.RandomCurrent.sources ends P = Sj ∆ T) ∨ (∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧ StatMech.Sharpness.RandomCurrent.sources ends P = Si ∆ T)) := by
-- proof
  apply StatMech.Ising.exists_lpReplica_sameProfile_targetSelector_counterexample

/--
[not_lpReplicaSameProfileTwoBranchSelectorPrinciple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSameProfileCounterexample.lean)
-/
@[path]
private lemma not_lpReplicaSameProfileTwoBranchSelectorPrinciple_eq :
-- imply
  ¬ LPReplicaSameProfileTwoBranchSelectorPrinciple := by
-- proof
  apply StatMech.Ising.not_lpReplicaSameProfileTwoBranchSelectorPrinciple


-- created on 2026-10-23
