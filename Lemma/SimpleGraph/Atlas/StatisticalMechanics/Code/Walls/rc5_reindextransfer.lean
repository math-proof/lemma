import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc5_reindextransfer
open Finset StatMech StatMech.Walls


/--
[rc5_filter_card_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reindextransfer.lean)
-/
@[path]
private lemma rc5_filter_card_congr_eq
  [Fintype E]
  [Fintype F]
  {g : E ≃ F}
  [DecidablePred P]
  [DecidablePred (fun y => P (g.symm y))]
-- given
  (P : E → Prop) :
-- imply
  #(univ.filter P) = #(univ.filter (fun y => P (g.symm y))) := by
-- proof
  apply StatMech.Walls.rc5_filter_card_congr g P

/--
[rc5_compl_cfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reindextransfer.lean)
-/
@[path]
private lemma rc5_compl_cfgEquiv_eq
  {e : E ≃ F}
  {ωf : ConfigSpace F} :
-- imply
  rmr_compl (cfgEquiv e ωf) = cfgEquiv e (rmr_compl ωf) := by
-- proof
  apply StatMech.Walls.rc5_compl_cfgEquiv e ωf

/--
[rc5_reindexTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reindextransfer.lean)
-/
@[path]
private lemma rc5_reindexTransfer_eq
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)}
-- given
  (hcard : ReimerCardFormAll) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc5_reindexTransfer hcard A B

/--
[rc5_reindexTransfer_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reindextransfer.lean)
-/
@[path]
private lemma rc5_reindexTransfer_inter_eq
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)}
-- given
  (hcard : ReimerCardFormAll) :
-- imply
  #(univ.filter (fun ω : ConfigSpace β => ω ∈ disjointOccurrence A B)) ≤ #(univ.filter (fun ω : ConfigSpace β => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc5_reindexTransfer_inter hcard A B


-- created on 2026-10-23
