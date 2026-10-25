import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ChordCut.Part5
open StatMech StatMech.Onsager StatMech.Onsager.ChordCut


/--
[cross_antisymm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma cross_antisymm_eq
  {a b : Pt} :
-- imply
  cross a b = - cross b a := by
-- proof
  apply StatMech.Onsager.ChordCut.cross_antisymm a b

/--
[reflex_continuation_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma reflex_continuation_interior_eq
  {din dout : Pt}
-- given
  (_hd : isDir din)
  (hrefl : cross din dout = -1) :
-- imply
  cross din din = 0 ∧ 0 < cross dout din := by
-- proof
  apply StatMech.Onsager.ChordCut.reflex_continuation_interior din dout _hd hrefl

/--
[convex_continuation_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma convex_continuation_exterior_eq
  {din dout : Pt}
-- given
  (hconv : cross din dout = 1) :
-- imply
  cross dout din < 0 := by
-- proof
  apply StatMech.Onsager.ChordCut.convex_continuation_exterior din dout hconv

/--
[continuation_not_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma continuation_not_exterior_eq
  {din : Pt}
-- given
  (hd : isDir din) :
-- imply
  din.1 * (-din).1 + din.2 * (-din).2 < 0 := by
-- proof
  apply StatMech.Onsager.ChordCut.continuation_not_exterior din hd

/--
[stopEvent_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma stopEvent_exists_eq
  {D : BoxData}
  {w : Pt}
-- given
  (hw : w ∈ D.B) :
-- imply
  ∃ k, stopEvent D w k := by
-- proof
  apply StatMech.Onsager.ChordCut.stopEvent_exists D w hw

/--
[chord_firstHit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma chord_firstHit_eq
  {D : BoxData}
  {w : Pt}
-- given
  (hw : w ∈ D.B) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ (rayX w k ∈ D.B ∨ D.x1 < w.1 + (k : ℤ)) ∧ (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B ∧ w.1 + (j : ℤ) ≤ D.x1) := by
-- proof
  apply StatMech.Onsager.ChordCut.chord_firstHit D w hw

/--
[rayX_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma rayX_injective_eq
  {w : Pt} :
-- imply
  Function.Injective (rayX w) := by
-- proof
  apply StatMech.Onsager.ChordCut.rayX_injective w

/--
[chordInterior_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma chordInterior_nodup_eq
  {w : Pt}
  {k : ℕ} :
-- imply
  (chordInterior w k).Nodup := by
-- proof
  apply StatMech.Onsager.ChordCut.chordInterior_nodup w k

/--
[chordInterior_disjoint_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma chordInterior_disjoint_boundary_eq
  {D : BoxData}
  {w : Pt}
  {k : ℕ}
  {arc : List Pt}
-- given
  (harc : ∀ p ∈ arc, p ∈ D.B)
  (hint : ∀ p ∈ chordInterior w k, p ∉ D.B) :
-- imply
  arc.Disjoint (chordInterior w k) := by
-- proof
  apply StatMech.Onsager.ChordCut.chordInterior_disjoint_boundary D w k arc harc hint

/--
[chordInterior_offBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma chordInterior_offBoundary_eq
  {D : BoxData}
  {w : Pt}
  {k : ℕ}
-- given
  (hfh : ∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B) :
-- imply
  ∀ p ∈ chordInterior w k, p ∉ D.B := by
-- proof
  apply StatMech.Onsager.ChordCut.chordInterior_offBoundary D w k hfh

/--
[chord_piece_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma chord_piece_nodup_eq
  {D : BoxData}
  {w : Pt}
  {k : ℕ}
  {arc : List Pt}
-- given
  (harcND : arc.Nodup)
  (harc : ∀ p ∈ arc, p ∈ D.B)
  (hint : ∀ p ∈ chordInterior w k, p ∉ D.B) :
-- imply
  (arc ++ chordInterior w k).Nodup := by
-- proof
  apply StatMech.Onsager.ChordCut.chord_piece_nodup D w k arc harcND harc hint

/--
[chord_of_interiorReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma chord_of_interiorReaches_eq
  {D : BoxData}
  {w : Pt}
-- given
  (_hw : w ∈ D.B)
  (hcore : InteriorReaches D w) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧ (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B) := by
-- proof
  apply StatMech.Onsager.ChordCut.chord_of_interiorReaches D w _hw hcore

/--
[chord_split_of_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean)
-/
@[path]
private lemma chord_split_of_core_eq
  {D : BoxData}
  {w : Pt}
  {arc : List Pt}
-- given
  (_hw : w ∈ D.B)
  (hcore : InteriorReaches D w)
  (harcND : arc.Nodup)
  (harc : ∀ p ∈ arc, p ∈ D.B) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧ (arc ++ chordInterior w k).Nodup := by
-- proof
  apply StatMech.Onsager.ChordCut.chord_split_of_core D w _hw hcore arc harcND harc


-- created on 2026-10-23
