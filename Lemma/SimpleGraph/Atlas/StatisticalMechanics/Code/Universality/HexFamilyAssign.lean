import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3
open StatMech StatMech.Universality


/--
[hexFam_omega_cube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexFam_omega_cube_eq :
-- imply
  hexOmega ^ 3 = 1 := by
-- proof
  apply StatMech.Universality.hexFam_omega_cube

/--
[hexFam_omega_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexFam_omega_ne_one_eq :
-- imply
  hexOmega ≠ 1 := by
-- proof
  apply StatMech.Universality.hexFam_omega_ne_one

/--
[hexFam_omega_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexFam_omega_sum_zero_eq :
-- imply
  (1 : ℂ) + hexOmega + hexOmega ^ 2 = 0 := by
-- proof
  apply StatMech.Universality.hexFam_omega_sum_zero

/--
[hexFam_hexUnit_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexFam_hexUnit_add_two_eq
-- given
  (h : ℤ) :
-- imply
  hexUnit (h + 2) = hexUnit h * hexOmega := by
-- proof
  apply StatMech.Universality.hexFam_hexUnit_add_two h

/--
[hexFam_part5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexFam_part5_eq
  [DecidableEq V]
  {s : Finset (HexIncidence V)}
  {cls : HexIncidence V → Fin 5} :
-- imply
  s = (s.filter (fun e => cls e = 0)) ∪ (s.filter (fun e => cls e = 1)) ∪ (s.filter (fun e => cls e = 2)) ∪ (s.filter (fun e => cls e = 3)) ∪ (s.filter (fun e => cls e = 4)) := by
-- proof
  apply StatMech.Universality.hexFam_part5 s cls

/--
[hexFam_disj5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexFam_disj5_eq
  [DecidableEq V]
  {s : Finset (HexIncidence V)}
  {cls : HexIncidence V → Fin 5}
  {a b : Fin 5}
-- given
  (hab : a ≠ b) :
-- imply
  Disjoint (s.filter (fun e => cls e = a)) (s.filter (fun e => cls e = b)) := by
-- proof
  apply StatMech.Universality.hexFam_disj5 s cls a b hab

/--
[hexFam_straightSide_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexFam_straightSide_dir_eq
  [DecidableEq V]
  {D : HexDomain V}
  {s : Finset (HexIncidence V)}
-- given
  (heading : V → Fin 3 → ℤ)
  (hgeom : ∀ v j, D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j))
  (h : ℤ)
  (hconst : ∀ e ∈ s, heading e.vtx e.edge = h) :
-- imply
  ∀ e ∈ s, D.mid e.vtx e.edge - D.pos e.vtx = (1 / 2 : ℂ) * hexUnit h := by
-- proof
  apply StatMech.Universality.hexFam_straightSide_dir D heading hgeom s h hconst

/--
[hexCell_geom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexCell_geom_eq
  {c : ℂ}
  {v : Fin 1}
  {j : Fin 3} :
-- imply
  (hexCell c).mid v j - (hexCell c).pos v = (1 / 2 : ℂ) * hexUnit (2 * (j : ℤ)) := by
-- proof
  apply StatMech.Universality.hexCell_geom c v j

/--
[hexCell_straightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexCell_straightSide_eq
  {c : ℂ}
  {j0 : Fin 3}
  {s : Finset (HexIncidence (Fin 1))}
-- given
  (hconst : ∀ e ∈ s, e.edge = j0) :
-- imply
  ∀ e ∈ s, (hexCell c).mid e.vtx e.edge - (hexCell c).pos e.vtx = (1 / 2 : ℂ) * hexUnit (2 * (j0 : ℤ)) := by
-- proof
  apply StatMech.Universality.hexCell_straightSide c j0 s hconst

/--
[hexBoundary_identity_via_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexBoundary_identity_via_family_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {F : HexFamilyData D P}
-- given
  (hsub : P.interior ⊆ D.incidences)
  (hFa : F.Fa = 1) :
-- imply
  hexBdryCl * F.lam + hexBdryCt * (F.taup + F.taum) + F.ups = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_identity_via_family D P hsub F hFa

/--
[hexBoundary_identity_scales_via_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean)
-/
@[path]
private lemma hexBoundary_identity_scales_via_family_eq
  [DecidableEq V]
  {D : ℕ → HexDomain V}
-- given
  (P : ∀ v, (D v).InteriorPairing)
  (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
  (F : ∀ v, HexFamilyData (D v) (P v))
  (hFa : ∀ v, 1 ≤ v → (F v).Fa = 1) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * (F v).lam + hexBdryCt * ((F v).taup + (F v).taum) + (F v).ups = 1 := by
-- proof
  apply StatMech.Universality.hexBoundary_identity_scales_via_family D P hsub F hFa


-- created on 2026-10-23
