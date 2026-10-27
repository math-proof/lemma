import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.InteriorReaches
open StatMech StatMech.Onsager StatMech.Onsager.InteriorReaches


/--
[separatedBy_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorReaches.lean)
-/
@[path]
private lemma separatedBy_of_covers_eq
  {D : BoxData}
  {S : Set Pt}
-- given
  (h : BoundaryCoversTransitions D S) :
-- imply
  SeparatedBy D S := by
-- proof
  apply StatMech.Onsager.InteriorReaches.separatedBy_of_covers D S h

/--
[shift_ray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorReaches.lean)
-/
@[path]
private lemma shift_ray_eq
  {w : Pt}
  {k : ℕ} :
-- imply
  ((rayX w k).1 + 1, (rayX w k).2) = rayX w (k + 1) := by
-- proof
  apply StatMech.Onsager.InteriorReaches.shift_ray w k

/--
[interiorReaches_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorReaches.lean)
-/
@[path]
private lemma interiorReaches_of_separated_eq
  {D : BoxData}
  {w : Pt}
  {S : Set Pt}
-- given
  (hbd : BoundedRight D S)
  (hsep : SeparatedBy D S)
  (hin : rayX w 1 ∈ S) :
-- imply
  InteriorReaches D w := by
-- proof
  apply StatMech.Onsager.InteriorReaches.interiorReaches_of_separated D w S hbd hsep hin

/--
[interiorReaches_of_polygon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorReaches.lean)
-/
@[path]
private lemma interiorReaches_of_polygon_eq
  {D : BoxData}
  {w : Pt}
  {S : Set Pt}
-- given
  (hbd : BoundedRight D S)
  (hcov : BoundaryCoversTransitions D S)
  (hin : rayX w 1 ∈ S) :
-- imply
  InteriorReaches D w := by
-- proof
  apply StatMech.Onsager.InteriorReaches.interiorReaches_of_polygon D w S hbd hcov hin

/--
[chord_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorReaches.lean)
-/
@[path]
private lemma chord_of_separated_eq
  {D : BoxData}
  {w : Pt}
  {S : Set Pt}
-- given
  (hw : w ∈ D.B)
  (hbd : BoundedRight D S)
  (hsep : SeparatedBy D S)
  (hin : rayX w 1 ∈ S) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧ (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B) := by
-- proof
  apply StatMech.Onsager.InteriorReaches.chord_of_separated D w hw S hbd hsep hin

/--
[chord_split_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorReaches.lean)
-/
@[path]
private lemma chord_split_of_separated_eq
  {D : BoxData}
  {w : Pt}
  {S : Set Pt}
  {arc : List Pt}
-- given
  (hw : w ∈ D.B)
  (hbd : BoundedRight D S)
  (hsep : SeparatedBy D S)
  (hin : rayX w 1 ∈ S)
  (harcND : arc.Nodup)
  (harc : ∀ p ∈ arc, p ∈ D.B) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧ (arc ++ chordInterior w k).Nodup := by
-- proof
  apply StatMech.Onsager.InteriorReaches.chord_split_of_separated D w hw S hbd hsep hin arc harcND harc


-- created on 2026-10-23
