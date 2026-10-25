import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialBondLabel.Part2
open StatMech StatMech.FrontierD


/--
[even_finitePeriodicSucc_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBondLabel.lean)
-/
@[path]
private lemma even_finitePeriodicSucc_iff_eq
  {R : FKRectTorus}
  {y : Fin R.height} :
-- imply
  Even (finitePeriodicSucc R.height_pos y).val ↔ ¬ Even y.val := by
-- proof
  apply StatMech.FrontierD.even_finitePeriodicSucc_iff R y

/--
[even_cyclicPred_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBondLabel.lean)
-/
@[path]
private lemma even_cyclicPred_iff_eq
  {R : FKRectTorus}
  {y : Fin R.height} :
-- imply
  Even (SixVertexArrows.cyclicPred R.height_pos y).val ↔ ¬ Even y.val := by
-- proof
  apply StatMech.FrontierD.even_cyclicPred_iff R y

/--
[finitePeriodicSucc_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBondLabel.lean)
-/
@[path]
private lemma finitePeriodicSucc_val_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N) :
-- imply
  (finitePeriodicSucc hN i).val = if i.val + 1 = N then 0 else i.val + 1 := by
-- proof
  apply StatMech.FrontierD.finitePeriodicSucc_val hN i

/--
[fkRectTorusMedialEdgeEquiv_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBondLabel.lean)
-/
@[path]
private lemma fkRectTorusMedialEdgeEquiv_bondMate_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectTorusMedialEdgeEquiv R (fkMedialBondMate R.medialTorus d).1 = fkRectMedialBondEdgeIndex R (fkRectTorusMedialEdgeEquiv R d.1) d.2 := by
-- proof
  apply StatMech.FrontierD.fkRectTorusMedialEdgeEquiv_bondMate R d

/--
[fkRectMedialDartPrimalLabel_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBondLabel.lean)
-/
@[path]
private lemma fkRectMedialDartPrimalLabel_bondMate_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDartPrimalLabel R (fkMedialBondMate R.medialTorus d) = fkRectMedialDartPrimalLabel R d := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDartPrimalLabel_bondMate R d


-- created on 2026-10-23
