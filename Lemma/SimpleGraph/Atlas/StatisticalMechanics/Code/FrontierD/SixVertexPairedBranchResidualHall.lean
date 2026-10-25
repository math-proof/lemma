import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
open Finset StatMech StatMech.FrontierD


/--
[SixVertexHorizontalPairedBranchResidualConstruction.target_inverseBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma target_inverseBranch_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {construction : SixVertexHorizontalPairedBranchResidualConstruction T middle hmiddle_pos hmiddle_lt grade}
  {output : SixVertexHorizontalActualSurplusTokens T grade (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle}
-- given
  (source : {source : SixVertexHorizontalActualDeficitTokens T grade (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle // exists branch, construction.target source branch = output}) :
-- imply
  construction.target source.1 (construction.inverseBranch output source) = output := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalPairedBranchResidualConstruction.target_inverseBranch construction output source

/--
[SixVertexHorizontalPairedBranchResidualAtlas.source_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma source_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalActualDeficitTokens T grade (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle} :
-- imply
  2 <= (Finset.univ.filter (SixVertexHorizontalPairedBranchResidualRelated atlas source)).card := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalPairedBranchResidualAtlas.source_degree atlas source

/--
[SixVertexHorizontalPairedBranchResidualAtlas.source_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma source_nonempty_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalActualDeficitTokens T grade (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle} :
-- imply
  (Finset.univ.filter (SixVertexHorizontalPairedBranchResidualRelated atlas source)).Nonempty := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalPairedBranchResidualAtlas.source_nonempty atlas source

/--
[SixVertexHorizontalPairedBranchResidualAtlas.inverse_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma inverse_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle hmiddle_pos hmiddle_lt grade}
  {target : SixVertexHorizontalActualSurplusTokens T grade (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle} :
-- imply
  (Finset.univ.filter fun source => SixVertexHorizontalPairedBranchResidualRelated atlas source target).card <= 2 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalPairedBranchResidualAtlas.inverse_degree atlas target

/--
[SixVertexHorizontalPairedBranchResidualAtlas.hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma hall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  forall sources : Finset (SixVertexHorizontalActualDeficitTokens T grade (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle), sources.card <= (Finset.univ.filter fun target => exists source, source ∈ sources ∧ SixVertexHorizontalPairedBranchResidualRelated atlas source target).card := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalPairedBranchResidualAtlas.hall atlas

/--
[pairedBranchResidualAtlases_of_constructions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma pairedBranchResidualAtlases_of_constructions_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
-- given
  (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalPairedBranchResidualAtlases T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.pairedBranchResidualAtlases_of_constructions hconstruction

/--
[offDiagonalTwoCycleMatching_of_pairedBranchConstructions_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma offDiagonalTwoCycleMatching_of_pairedBranchConstructions_direct_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
-- given
  (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.offDiagonalTwoCycleMatching_of_pairedBranchConstructions_direct hconstruction

/--
[pairedBranchResidualConstructions_of_nonempty_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma pairedBranchResidualConstructions_of_nonempty_sources_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
-- given
  (hconstruction : forall grade : Nat × Nat, Nonempty (SixVertexHorizontalActualDeficitTokens T grade (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) -> Nonempty (SixVertexHorizontalPairedBranchResidualConstruction T middle hmiddle_pos hmiddle_lt grade)) :
-- imply
  SixVertexHorizontalPairedBranchResidualConstructions T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.pairedBranchResidualConstructions_of_nonempty_sources hconstruction

/--
[offDiagonalTwoCycleMatching_of_pairedBranchAtlases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma offDiagonalTwoCycleMatching_of_pairedBranchAtlases_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
-- given
  (hatlas : SixVertexHorizontalPairedBranchResidualAtlases T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.offDiagonalTwoCycleMatching_of_pairedBranchAtlases hatlas

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchAtlases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchAtlases_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hatlas : SixVertexHorizontalPairedBranchResidualAtlases T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchAtlases T middle hmiddle_pos hmiddle_lt hatlas

/--
[sixVertexSectorTrace_logConcave_of_pairedBranchAtlases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_pairedBranchAtlases_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (hatlas : SixVertexHorizontalPairedBranchResidualAtlases T middle hmiddle_pos hmiddle_lt) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_pairedBranchAtlases T middle hmiddle_pos hmiddle_lt hc hatlas

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchConstructions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchConstructions_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchConstructions T middle hmiddle_pos hmiddle_lt hconstruction

/--
[sixVertexSectorTrace_logConcave_of_pairedBranchConstructions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_pairedBranchConstructions_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions T middle hmiddle_pos hmiddle_lt) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_pairedBranchConstructions T middle hmiddle_pos hmiddle_lt hc hconstruction


-- created on 2026-10-23
