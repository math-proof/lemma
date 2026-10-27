import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc80bookroute
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc80_sharpResidue_iff_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc80bookroute.lean)
-/
@[path]
private lemma gc80_sharpResidue_iff_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  gc38_SharpGHSResidue G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc80_sharpResidue_iff_ghs G β h o x y

/--
[gc80_routeA_residue_iff_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc80bookroute.lean)
-/
@[path]
private lemma gc80_routeA_residue_iff_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc39_ThreeReplicaImprovedBound G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc80_routeA_residue_iff_ghs G β h hβ hh o x y hox hoy hxy

/--
[gc80_routeB_closes_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc80bookroute.lean)
-/
@[path]
private lemma gc80_routeB_closes_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hres : gc25_NativeResummation G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc80_routeB_closes_ghs G β h hβ hh o x y hox hoy hxy hres

/--
[gc80_routeB_closes_routeA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc80bookroute.lean)
-/
@[path]
private lemma gc80_routeB_closes_routeA_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hres : gc25_NativeResummation G β h o x y) :
-- imply
  gc39_ThreeReplicaImprovedBound G β h o x y := by
-- proof
  apply StatMech.Walls.gc80_routeB_closes_routeA G β h hβ hh o x y hox hoy hxy hres

/--
[gc80_routeB_is_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc80bookroute.lean)
-/
@[path]
private lemma gc80_routeB_is_identity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc25_NativeResummation G β h o x y ↔ (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = -2 * gc25_nativeAllConnMass G β h o x y := by
-- proof
  apply StatMech.Walls.gc80_routeB_is_identity G β h o x y hox hoy hxy

/--
[gc80_routeA_closes_ghsSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc80bookroute.lean)
-/
@[path]
private lemma gc80_routeA_closes_ghsSym_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc39_ThreeReplicaImprovedBound G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc80_routeA_closes_ghsSym G β h hβ hh o hres

/--
[gc80_routeB_closes_ghsSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc80bookroute.lean)
-/
@[path]
private lemma gc80_routeB_closes_ghsSym_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc80_routeB_closes_ghsSym G β h hβ hh o hres

/--
[gc80_routeA_ghs_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc80bookroute.lean)
-/
@[path]
private lemma gc80_routeA_ghs_at_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc39_ThreeReplicaImprovedBound G β 0 o x y ∧ eg_ursell3 G β 0 o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc80_routeA_ghs_at_zero G β hβ o x y hox hoy hxy

/--
[gc80_bookroute_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc80bookroute.lean)
-/
@[path]
private lemma gc80_bookroute_status_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  (∀ x y : V, o ≠ x → o ≠ y → x ≠ y → (gc39_ThreeReplicaImprovedBound G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0)) ∧ (∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y → eg_ursell3 G β h o x y ≤ 0) ∧ (∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y → gc39_ThreeReplicaImprovedBound G β h o x y) ∧ ((∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc39_ThreeReplicaImprovedBound G β h o x y) → GHSThreePointSym G β h o) ∧ ((∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y) → GHSThreePointSym G β h o) := by
-- proof
  apply StatMech.Walls.gc80_bookroute_status G β h hβ hh o


-- created on 2026-10-23
