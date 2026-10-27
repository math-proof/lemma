import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall.Part4
open Finset StatMech StatMech.FrontierD


/--
[SixVertexConfigurationPairedBranchEmbeddings.source_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean)
-/
@[path]
private lemma source_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexConfigurationPairBigradeFiber T (sixVertexConfigurationLowerSector middle hmiddle_pos) (sixVertexConfigurationUpperSector middle hmiddle_lt) grade} :
-- imply
  2 <= (Finset.univ.filter (SixVertexConfigurationPairedBranchRelated embeddings source)).card := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPairedBranchEmbeddings.source_degree embeddings source

/--
[SixVertexConfigurationPairedBranchEmbeddings.branch_inverseBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean)
-/
@[path]
private lemma branch_inverseBranch_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle hmiddle_pos hmiddle_lt grade}
  {target : SixVertexConfigurationPairBigradeFiber T middle middle grade}
  {source : {source : SixVertexConfigurationPairBigradeFiber T (sixVertexConfigurationLowerSector middle hmiddle_pos) (sixVertexConfigurationUpperSector middle hmiddle_lt) grade // SixVertexConfigurationPairedBranchRelated embeddings source target}} :
-- imply
  embeddings.branch (embeddings.inverseBranch target source) source.1 = target := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPairedBranchEmbeddings.branch_inverseBranch embeddings target source

/--
[SixVertexConfigurationPairedBranchEmbeddings.inverse_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean)
-/
@[path]
private lemma inverse_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle hmiddle_pos hmiddle_lt grade}
  {target : SixVertexConfigurationPairBigradeFiber T middle middle grade} :
-- imply
  (Finset.univ.filter fun source => SixVertexConfigurationPairedBranchRelated embeddings source target).card <= 2 := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPairedBranchEmbeddings.inverse_degree embeddings target

/--
[SixVertexConfigurationPairedBranchEmbeddings.hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean)
-/
@[path]
private lemma hall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  forall sources : Finset (SixVertexConfigurationPairBigradeFiber T (sixVertexConfigurationLowerSector middle hmiddle_pos) (sixVertexConfigurationUpperSector middle hmiddle_lt) grade), sources.card <= (Finset.univ.filter fun target => exists source, source ∈ sources ∧ SixVertexConfigurationPairedBranchRelated embeddings source target).card := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPairedBranchEmbeddings.hall embeddings

/--
[configurationPairedBranchConstructions_of_nonempty_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean)
-/
@[path]
private lemma configurationPairedBranchConstructions_of_nonempty_sources_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
-- given
  (hconstruction : forall grade, Nonempty (SixVertexConfigurationPairBigradeFiber T (sixVertexConfigurationLowerSector middle hmiddle_pos) (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) -> Nonempty (SixVertexConfigurationPairedBranchGeometricConstruction T middle hmiddle_pos hmiddle_lt grade)) :
-- imply
  SixVertexConfigurationPairedBranchConstructions T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.configurationPairedBranchConstructions_of_nonempty_sources hconstruction

/--
[configurationBigradeFibers_of_pairedBranchConstructions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean)
-/
@[path]
private lemma configurationBigradeFibers_of_pairedBranchConstructions_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
-- given
  (hconstruction : SixVertexConfigurationPairedBranchConstructions T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexConfigurationPairBigradeFiberDominates T (sixVertexConfigurationLowerSector middle hmiddle_pos) (sixVertexConfigurationUpperSector middle hmiddle_lt) middle middle := by
-- proof
  apply StatMech.FrontierD.configurationBigradeFibers_of_pairedBranchConstructions hconstruction

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationPairedBranches_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hconstruction : SixVertexConfigurationPairedBranchConstructions T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationPairedBranches T middle hmiddle_pos hmiddle_lt hconstruction

/--
[sixVertexSectorTrace_logConcave_of_configurationPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_configurationPairedBranches_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (hconstruction : SixVertexConfigurationPairedBranchConstructions T middle hmiddle_pos hmiddle_lt) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_configurationPairedBranches T middle hmiddle_pos hmiddle_lt hc hconstruction


-- created on 2026-10-23
