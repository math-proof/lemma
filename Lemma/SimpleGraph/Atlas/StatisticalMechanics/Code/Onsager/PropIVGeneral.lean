import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.PropIVGeneral
open StatMech StatMech.Onsager StatMech.Onsager.PropIVGeneral


/--
[fromSite_toSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma fromSite_toSite_eq
  {p : Pt} :
-- imply
  fromSite (toSite p) = p := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.fromSite_toSite p

/--
[toSite_fromSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma toSite_fromSite_eq
  {x : Site 2} :
-- imply
  toSite (fromSite x) = x := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.toSite_fromSite x

/--
[mem_interiorSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma mem_interiorSet_eq
  {Q : Polygon}
  {p : Pt} :
-- imply
  toSite p ∈ interiorSet Q ↔ Odd (rayCross Q p) := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.mem_interiorSet Q p

/--
[interiorSet_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma interiorSet_eq_image_eq
  {Q : Polygon} :
-- imply
  interiorSet Q = toSite '' preInterior Q := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.interiorSet_eq_image Q

/--
[rayCross_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma rayCross_shift_eq
  {Q : Polygon}
  {p : Pt} :
-- imply
  rayCross Q (p.1 + 1, p.2) = (Q.filter (fun q => q.2 = p.2 ∧ p.1 + 1 ≤ q.1)).card := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.rayCross_shift Q p

/--
[rayCross_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma rayCross_step_eq
  {Q : Polygon}
  {p : Pt} :
-- imply
  rayCross Q p = (if p ∈ Q then 1 else 0) + rayCross Q (p.1 + 1, p.2) := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.rayCross_step Q p

/--
[rayCross_add_leftCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma rayCross_add_leftCross_eq
  {Q : Polygon}
  {p : Pt} :
-- imply
  rayCross Q p + leftCross Q p = rowCount Q p.2 := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.rayCross_add_leftCross Q p

/--
[Bset_interiorSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma Bset_interiorSet_eq
  {Q : Polygon} :
-- imply
  Bset (interiorSet Q) = (↑Q : Set Pt) := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.Bset_interiorSet Q

/--
[trap_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma trap_finite_eq
  {a b c : ℤ} :
-- imply
  {p : Pt | a < p.1 ∧ p.1 ≤ b ∧ p.2 = c}.Finite := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.trap_finite a b c

/--
[preInterior_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma preInterior_finite_eq
  {Q : Polygon}
-- given
  (hcl : IsClosedPolygon Q) :
-- imply
  (preInterior Q).Finite := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.preInterior_finite Q hcl

/--
[interior_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma interior_finite_eq
  {Q : Polygon}
-- given
  (hcl : IsClosedPolygon Q) :
-- imply
  (interiorSet Q).Finite := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.interior_finite Q hcl

/--
[rayCast_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma rayCast_parity_eq
  {Q : Polygon}
  {p : Pt}
  {N : ℕ}
-- given
  (hout : toSite (rayX p N) ∉ interiorSet Q) :
-- imply
  toSite p ∈ interiorSet Q ↔ ¬ Even (crossCount (interiorSet Q) (rayWalk p N)) := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.rayCast_parity Q p N hout

/--
[chord_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma chord_general_eq
  {Q : Polygon}
  {w : Pt}
-- given
  (hcl : IsClosedPolygon Q)
  (hw : w ∈ Q)
  (hlaunch : Odd (rayCross Q (w.1 + 1, w.2))) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ (mkBoxData (interiorSet Q) (interior_finite Q hcl)).B ∧ (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ (mkBoxData (interiorSet Q) (interior_finite Q hcl)).B) := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.chord_general Q hcl w hw hlaunch

/--
[interiorReaches_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean)
-/
@[path]
private lemma interiorReaches_general_eq
  {Q : Polygon}
  {w : Pt}
-- given
  (hcl : IsClosedPolygon Q)
  (hlaunch : Odd (rayCross Q (w.1 + 1, w.2))) :
-- imply
  InteriorReaches (mkBoxData (interiorSet Q) (interior_finite Q hcl)) w := by
-- proof
  apply StatMech.Onsager.PropIVGeneral.interiorReaches_general Q hcl w hlaunch


-- created on 2026-10-23
