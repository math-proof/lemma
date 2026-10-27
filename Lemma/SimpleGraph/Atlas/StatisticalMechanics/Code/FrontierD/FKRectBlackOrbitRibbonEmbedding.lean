import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part5
open StatMech StatMech.FrontierD


/--
[fkRectRibbonCellResidueEmbed_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonCellResidueEmbed_injective_eq
  {M : ℕ}
-- given
  (_hM : 0 < M) :
-- imply
  Function.Injective (fkRectRibbonCellResidueEmbed M) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonCellResidueEmbed_injective M _hM

/--
[fkRectRibbonCellResidueEmbed_normalize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonCellResidueEmbed_normalize_eq
  {M : ℕ}
  {i : Fin M}
  {o : Int}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonCellResidueEmbed M (fkRectRibbonNormalizeCell hM i o) = (((8 * i.val : Nat) : Int) + o : ZMod (8 * M)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonCellResidueEmbed_normalize hM i o

/--
[fkRectRibbonNormalizeCell_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_slot_eq
  {M : ℕ}
  {i : Fin M}
  {r : Fin 8}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i (r.val : Int) = (i, r) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_slot hM i r

/--
[fkRectRibbonNormalizeCell_slot_add_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_slot_add_eight_eq
  {M : ℕ}
  {i : Fin M}
  {r : Fin 8}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i (8 + r.val : Int) = (finitePeriodicSucc hM i, r) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_slot_add_eight hM i r

/--
[fkRectRibbonNormalizeCell_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_neg_one_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i (-1) = (SixVertexArrows.cyclicPred hM i, (7 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_neg_one hM i

/--
[fkRectRibbonNormalizeCell_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_zero_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 0 = (i, (0 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_zero hM i

/--
[fkRectRibbonNormalizeCell_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_one_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 1 = (i, (1 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_one hM i

/--
[fkRectRibbonNormalizeCell_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_two_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 2 = (i, (2 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_two hM i

/--
[fkRectRibbonNormalizeCell_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_three_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 3 = (i, (3 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_three hM i

/--
[fkRectRibbonNormalizeCell_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_four_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 4 = (i, (4 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_four hM i

/--
[fkRectRibbonNormalizeCell_five](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_five_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 5 = (i, (5 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_five hM i

/--
[fkRectRibbonNormalizeCell_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_six_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 6 = (i, (6 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_six hM i

/--
[fkRectRibbonNormalizeCell_seven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_seven_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 7 = (i, (7 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_seven hM i

/--
[fkRectRibbonNormalizeCell_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_eight_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 8 = (finitePeriodicSucc hM i, (0 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_eight hM i

/--
[fkRectRibbonNormalizeCell_nine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectRibbonNormalizeCell_nine_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectRibbonNormalizeCell hM i 9 = (finitePeriodicSucc hM i, (1 : Fin 8)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonNormalizeCell_nine hM i

/--
[fkRectMedialRibbonBlockOffset_eq_table](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlockOffset_eq_table_eq
  {pairing : Bool}
  {side : FKMedialSide} :
-- imply
  fkRectMedialRibbonBlockOffset pairing side = fkRectMedialRibbonBlockOffsetTable pairing side := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlockOffset_eq_table pairing side

/--
[fkRectMedialRibbonBlockCode_embed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlockCode_embed_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus}
  {t : Fin 8} :
-- imply
  (fkRectRibbonCellResidueEmbed R.medialTorus.width (fkRectMedialRibbonBlockCode R pairing d t).1, fkRectRibbonCellResidueEmbed R.medialTorus.height (fkRectMedialRibbonBlockCode R pairing d t).2) = fkRectMedialRibbonBlockSite R pairing d t := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlockCode_embed R pairing d t

/--
[fkRectMedialRibbonBlockCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlockCode_injective_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus} :
-- imply
  Function.Injective (fun z : FKMedialBlackDart R.medialTorus × Fin 8 => fkRectMedialRibbonBlockCode R pairing z.1 z.2) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlockCode_injective R pairing

/--
[fkRectMedialRibbonBlockSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlockSite_injective_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus} :
-- imply
  Function.Injective (fun z : FKMedialBlackDart R.medialTorus × Fin 8 => fkRectMedialRibbonBlockSite R pairing z.1 z.2) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlockSite_injective R pairing

/--
[fkRectBlackOrbitMedialRibbonIndexedSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonIndexedSite_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  Function.Injective (fkRectBlackOrbitMedialRibbonIndexedSite R omega d) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonIndexedSite_injective R omega d

/--
[fkRectMedialRibbonBlockDirection_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlockDirection_apply_eq
  {pairing : Bool}
  {side : FKMedialSide}
  {t : Fin 8} :
-- imply
  fkRectMedialRibbonBlockDirection pairing side t = (fkRectMedialRibbonBlock pairing side).get ⟨t.val, by simpa only [fkRectMedialRibbonBlock_length] using t.isLt⟩ := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlockDirection_apply pairing side t


-- created on 2026-10-23
