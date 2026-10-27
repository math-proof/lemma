import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
open Finset StatMech StatMech.FrontierA


/--
[cubicalCellFaces_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma cubicalCellFaces_isClosed_eq
  {a b c : Nat}
  {q : CubicalCell a b c} :
-- imply
  IsClosedPlaquetteSet cubicalPlaquetteIncidence (cubicalCellFaces q) := by
-- proof
  apply StatMech.FrontierA.cubicalCellFaces_isClosed q

/--
[closed_not_mem_of_unique_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma closed_not_mem_of_unique_incident_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype P]
  [DecidableEq P]
  {incidence : P → Finset E}
  {A : Finset P}
  {p : P}
  {e : E}
-- given
  (hclosed : IsClosedPlaquetteSet incidence A)
  (hpe : e ∈ incidence p)
  (hunique : ∀ q ∈ A, e ∈ incidence q → q = p) :
-- imply
  p ∉ A := by
-- proof
  apply StatMech.FrontierA.closed_not_mem_of_unique_incident incidence A hclosed p e hpe hunique

/--
[gaugeSurfaceBoundary_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma gaugeSurfaceBoundary_symmDiff_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype P]
  [DecidableEq P]
  {incidence : P → Finset E}
  {A B : Finset P} :
-- imply
  gaugeSurfaceBoundary incidence (A ∆ B) = gaugeSurfaceBoundary incidence A ∆ gaugeSurfaceBoundary incidence B := by
-- proof
  apply StatMech.FrontierA.gaugeSurfaceBoundary_symmDiff incidence A B

/--
[gaugeSurfaceBoundary_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma gaugeSurfaceBoundary_insert_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype P]
  [DecidableEq P]
  {incidence : P → Finset E}
  {A : Finset P}
  {p : P}
-- given
  (hp : p ∉ A) :
-- imply
  gaugeSurfaceBoundary incidence (insert p A) = incidence p ∆ gaugeSurfaceBoundary incidence A := by
-- proof
  apply StatMech.FrontierA.gaugeSurfaceBoundary_insert incidence A p hp

/--
[cubicalVolumeBoundary_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma cubicalVolumeBoundary_isClosed_eq
  {a b c : Nat}
  {S : Finset (CubicalCell a b c)} :
-- imply
  IsClosedPlaquetteSet cubicalPlaquetteIncidence (cubicalVolumeBoundary S) := by
-- proof
  apply StatMech.FrontierA.cubicalVolumeBoundary_isClosed S

/--
[not_mem_of_even_unique_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma not_mem_of_even_unique_incident_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype P]
  [DecidableEq P]
  {incidence : P → Finset E}
  {A : Finset P}
  {p : P}
  {e : E}
-- given
  (hpe : e ∈ incidence p)
  (heven : Even (plaquetteIncidenceCount incidence A e))
  (hunique : ∀ q ∈ A, e ∈ incidence q → q = p) :
-- imply
  p ∉ A := by
-- proof
  apply StatMech.FrontierA.not_mem_of_even_unique_incident incidence A p e hpe heven hunique

/--
[volume_eq_empty_of_lowerXY_boundary_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma volume_eq_empty_of_lowerXY_boundary_not_mem_eq
  {a b c : Nat}
  {S : Finset (CubicalCell a b c)}
-- given
  (hc : 0 < c)
  (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c), CubicalPlaquette.xy i j k.castSucc ∉ cubicalVolumeBoundary S) :
-- imply
  S = ∅ := by
-- proof
  apply StatMech.FrontierA.volume_eq_empty_of_lowerXY_boundary_not_mem hc S hxy

/--
[closed_xz_not_mem_of_lowerXY_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma closed_xz_not_mem_of_lowerXY_not_mem_eq
  {a b c : Nat}
  {A : Finset (CubicalPlaquette a b c)}
-- given
  (hc : 0 < c)
  (hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence A)
  (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c), CubicalPlaquette.xy i j k.castSucc ∉ A) :
-- imply
  ∀ (i : Fin a) (j : Fin (b + 1)) (k : Fin c), CubicalPlaquette.xz i j k ∉ A := by
-- proof
  apply StatMech.FrontierA.closed_xz_not_mem_of_lowerXY_not_mem hc A hclosed hxy

/--
[closed_yz_not_mem_of_lowerXY_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma closed_yz_not_mem_of_lowerXY_not_mem_eq
  {a b c : Nat}
  {A : Finset (CubicalPlaquette a b c)}
-- given
  (hc : 0 < c)
  (hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence A)
  (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c), CubicalPlaquette.xy i j k.castSucc ∉ A) :
-- imply
  ∀ (i : Fin (a + 1)) (j : Fin b) (k : Fin c), CubicalPlaquette.yz i j k ∉ A := by
-- proof
  apply StatMech.FrontierA.closed_yz_not_mem_of_lowerXY_not_mem hc A hclosed hxy

/--
[closed_topXY_not_mem_of_lowerXY_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma closed_topXY_not_mem_of_lowerXY_not_mem_eq
  {a b c : Nat}
  {A : Finset (CubicalPlaquette a b c)}
-- given
  (hb : 0 < b)
  (hc : 0 < c)
  (hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence A)
  (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c), CubicalPlaquette.xy i j k.castSucc ∉ A)
  (hxz : ∀ (i : Fin a) (j : Fin (b + 1)) (k : Fin c), CubicalPlaquette.xz i j k ∉ A) :
-- imply
  ∀ (i : Fin a) (j : Fin b), CubicalPlaquette.xy i j (Fin.last c) ∉ A := by
-- proof
  apply StatMech.FrontierA.closed_topXY_not_mem_of_lowerXY_not_mem hb hc A hclosed hxy hxz

/--
[closed_eq_empty_of_lowerXY_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean)
-/
@[path]
private lemma closed_eq_empty_of_lowerXY_not_mem_eq
  {a b c : Nat}
  {A : Finset (CubicalPlaquette a b c)}
-- given
  (hb : 0 < b)
  (hc : 0 < c)
  (hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence A)
  (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c), CubicalPlaquette.xy i j k.castSucc ∉ A) :
-- imply
  A = ∅ := by
-- proof
  apply StatMech.FrontierA.closed_eq_empty_of_lowerXY_not_mem hb hc A hclosed hxy


-- created on 2026-10-23
