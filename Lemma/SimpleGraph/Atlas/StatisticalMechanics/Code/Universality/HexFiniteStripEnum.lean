import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
open StatMech StatMech.Universality


/--
[hexStrip_vert_eq_mid_plus_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_vert_eq_mid_plus_step_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  ∀ x ∈ verticesAux m h ts, ∃ mm ∈ midsAux m h ts, ∃ hh : ℤ, x = mm + halfStep hh := by
-- proof
  apply StatMech.Universality.hexStrip_vert_eq_mid_plus_step m h ts

/--
[hexStrip_vertex_mem_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_vertex_mem_eq_eq
  {w : HexWalk} :
-- imply
  ∀ x ∈ w.vertices, ∃ mm ∈ w.mids, ∃ hh : ℤ, x = mm + halfStep hh := by
-- proof
  apply StatMech.Universality.hexStrip_vertex_mem_eq w

/--
[hexStrip_halfStep_add6](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_halfStep_add6_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h + 6) = halfStep h := by
-- proof
  apply StatMech.Universality.hexStrip_halfStep_add6 h

/--
[hexStrip_halfStep_mod6](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_halfStep_mod6_eq
-- given
  (h : ℤ) :
-- imply
  halfStep h = halfStep (h % 6) := by
-- proof
  apply StatMech.Universality.hexStrip_halfStep_mod6 h

/--
[hexStrip_norm_halfStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_norm_halfStep_eq
-- given
  (h : ℤ) :
-- imply
  ‖halfStep h‖ = 1 / 2 := by
-- proof
  apply StatMech.Universality.hexStrip_norm_halfStep h

/--
[hexStrip_dist_vert_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_dist_vert_mid_eq
  {mm : ℂ}
-- given
  (hh : ℤ) :
-- imply
  dist (mm + halfStep hh) mm = 1 / 2 := by
-- proof
  apply StatMech.Universality.hexStrip_dist_vert_mid mm hh

/--
[hexStrip_mem_verts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_mem_verts_eq
  {M : Finset ℂ}
  {mm : ℂ}
-- given
  (hmm : mm ∈ M)
  (hh : ℤ) :
-- imply
  mm + halfStep hh ∈ hexStrip_verts M := by
-- proof
  apply StatMech.Universality.hexStrip_mem_verts M hmm hh

/--
[hexStrip_vertexBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_vertexBound_eq
  {M : Finset ℂ}
  {w : HexWalk}
-- given
  (hstay : ∀ m ∈ w.mids, m ∈ M) :
-- imply
  ∀ x ∈ w.vertices, x ∈ hexStrip_verts M := by
-- proof
  apply StatMech.Universality.hexStrip_vertexBound M w hstay

/--
[hexStrip_finiteRegion_mids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_finiteRegion_mids_eq
  {M : Finset ℂ}
  {a : ℂ}
-- given
  (ha : a ∈ M) :
-- imply
  (hexStrip_finiteRegion M a ha).mids = M := by
-- proof
  apply StatMech.Universality.hexStrip_finiteRegion_mids M a ha

/--
[hexStrip_finiteRegion_verts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_finiteRegion_verts_eq
  {M : Finset ℂ}
  {a : ℂ}
-- given
  (ha : a ∈ M) :
-- imply
  (hexStrip_finiteRegion M a ha).verts = hexStrip_verts M := by
-- proof
  apply StatMech.Universality.hexStrip_finiteRegion_verts M a ha

/--
[hexStrip_finiteRegion_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_finiteRegion_start_eq
  {M : Finset ℂ}
  {a : ℂ}
-- given
  (ha : a ∈ M) :
-- imply
  (hexStrip_finiteRegion M a ha).start = a := by
-- proof
  apply StatMech.Universality.hexStrip_finiteRegion_start M a ha

/--
[hexStrip_finiteRegion_inRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_finiteRegion_inRegion_iff_eq
  {M : Finset ℂ}
  {a : ℂ}
  {z : ℂ}
-- given
  (ha : a ∈ M) :
-- imply
  (hexStrip_finiteRegion M a ha).inRegion z ↔ z ∈ M := by
-- proof
  apply StatMech.Universality.hexStrip_finiteRegion_inRegion_iff M a ha z

/--
[hexStrip_finiteRegion_length_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_finiteRegion_length_lt_eq
  {M : Finset ℂ}
  {a : ℂ}
  {ts : List ℤ}
-- given
  (ha : a ∈ M)
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).IsSAW)
  (hstay : (ofTurns a h0 ts).StaysIn (hexStrip_finiteRegion M a ha).inRegion) :
-- imply
  ts.length < (hexStrip_verts M).card := by
-- proof
  apply StatMech.Universality.hexStrip_finiteRegion_length_lt M a ha h0 ts hsaw hstay

/--
[hexStrip_vertexBound_of_superset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_vertexBound_of_superset_eq
  {M : Finset ℂ}
  {verts : Finset ℂ}
  {w : HexWalk}
-- given
  (hsub : hexStrip_verts M ⊆ verts)
  (hstay : ∀ m ∈ w.mids, m ∈ M) :
-- imply
  ∀ x ∈ w.vertices, x ∈ verts := by
-- proof
  apply StatMech.Universality.hexStrip_vertexBound_of_superset M verts hsub w hstay

/--
[hexStrip_finiteRegion_of_superset_verts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_finiteRegion_of_superset_verts_eq
  {M verts : Finset ℂ}
  {a : ℂ}
-- given
  (ha : a ∈ M)
  (hsub : hexStrip_verts M ⊆ verts) :
-- imply
  (hexStrip_finiteRegion_of_superset M verts a ha hsub).verts = verts := by
-- proof
  apply StatMech.Universality.hexStrip_finiteRegion_of_superset_verts M verts a ha hsub

/--
[hexStrip_finiteRegion_of_superset_mids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_finiteRegion_of_superset_mids_eq
  {M verts : Finset ℂ}
  {a : ℂ}
-- given
  (ha : a ∈ M)
  (hsub : hexStrip_verts M ⊆ verts) :
-- imply
  (hexStrip_finiteRegion_of_superset M verts a ha hsub).mids = M := by
-- proof
  apply StatMech.Universality.hexStrip_finiteRegion_of_superset_mids M verts a ha hsub

/--
[hexStrip_region_finiteRegion_mids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_region_finiteRegion_mids_eq
  {R : HexRegion}
  {M : Finset ℂ}
-- given
  (ha : R.start ∈ M) :
-- imply
  (hexStrip_region_finiteRegion R M ha).mids = M := by
-- proof
  apply StatMech.Universality.hexStrip_region_finiteRegion_mids R M ha

/--
[hexStrip_region_finiteRegion_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_region_finiteRegion_start_eq
  {R : HexRegion}
  {M : Finset ℂ}
-- given
  (ha : R.start ∈ M) :
-- imply
  (hexStrip_region_finiteRegion R M ha).start = R.start := by
-- proof
  apply StatMech.Universality.hexStrip_region_finiteRegion_start R M ha

/--
[hexStrip_region_finiteRegion_verts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_region_finiteRegion_verts_eq
  {R : HexRegion}
  {M : Finset ℂ}
-- given
  (ha : R.start ∈ M) :
-- imply
  (hexStrip_region_finiteRegion R M ha).verts = hexStrip_verts M := by
-- proof
  apply StatMech.Universality.hexStrip_region_finiteRegion_verts R M ha

/--
[hexStrip_single_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_single_closure_eq
  {a : ℂ}
  {w : HexWalk}
-- given
  (hstay : ∀ m ∈ w.mids, m ∈ ({a} : Finset ℂ)) :
-- imply
  ∀ x ∈ w.vertices, x ∈ hexStrip_verts ({a} : Finset ℂ) := by
-- proof
  apply StatMech.Universality.hexStrip_single_closure a w hstay

/--
[hexStrip_singleRegion_mids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_singleRegion_mids_eq
  {a : ℂ} :
-- imply
  (hexStrip_singleRegion a).mids = ({a} : Finset ℂ) := by
-- proof
  apply StatMech.Universality.hexStrip_singleRegion_mids a

/--
[hexStrip_singleRegion_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean)
-/
@[path]
private lemma hexStrip_singleRegion_start_eq
  {a : ℂ} :
-- imply
  (hexStrip_singleRegion a).start = a := by
-- proof
  apply StatMech.Universality.hexStrip_singleRegion_start a


-- created on 2026-10-23
