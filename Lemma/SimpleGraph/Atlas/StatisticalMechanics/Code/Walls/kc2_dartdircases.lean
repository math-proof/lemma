import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc2_dartdircases
open SimpleGraph Function StatMech StatMech.Walls


/--
[kc2_mem_dirSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_mem_dirSet_eq
  {d : Site 2} :
-- imply
  d ∈ kc2_dirSet ↔ d = ![1, 0] ∨ d = ![-1, 0] ∨ d = ![0, 1] ∨ d = ![0, -1] := by
-- proof
  apply StatMech.Walls.kc2_mem_dirSet d

/--
[kc2_dirSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_dirSet_card_eq :
-- imply
  kc2_dirSet.card = 4 := by
-- proof
  apply StatMech.Walls.kc2_dirSet_card

/--
[kc2_unitWt_cardinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_unitWt_cardinal_eq :
-- imply
  unitWt (![1, 0] : Site 2) = 1 ∧ unitWt (![-1, 0] : Site 2) = 1 ∧ unitWt (![0, 1] : Site 2) = 1 ∧ unitWt (![0, -1] : Site 2) = 1 := by
-- proof
  apply StatMech.Walls.kc2_unitWt_cardinal

/--
[kc2_unitWt_one_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_unitWt_one_cases_eq
  {d : Site 2}
-- given
  (hd : unitWt d = 1) :
-- imply
  d = ![1, 0] ∨ d = ![-1, 0] ∨ d = ![0, 1] ∨ d = ![0, -1] := by
-- proof
  apply StatMech.Walls.kc2_unitWt_one_cases d hd

/--
[kc2_unitWt_one_mem_dirSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_unitWt_one_mem_dirSet_eq
  {d : Site 2}
-- given
  (hd : unitWt d = 1) :
-- imply
  d ∈ kc2_dirSet := by
-- proof
  apply StatMech.Walls.kc2_unitWt_one_mem_dirSet d hd

/--
[kc2_unitWt_one_rec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_unitWt_one_rec_eq
  {P : Prop}
  {d : Site 2}
-- given
  (hd : unitWt d = 1)
  (h0 : d = ![1, 0] → P)
  (h1 : d = ![-1, 0] → P)
  (h2 : d = ![0, 1] → P)
  (h3 : d = ![0, -1] → P) :
-- imply
  P := by
-- proof
  apply StatMech.Walls.kc2_unitWt_one_rec d hd h0 h1 h2 h3

/--
[kc2_dart_dir_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_dart_dir_cases_eq
  {e : Dart} :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
-- proof
  apply StatMech.Walls.kc2_dart_dir_cases e

/--
[kc2_dart_dir_mem_dirSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_dart_dir_mem_dirSet_eq
  {e : Dart} :
-- imply
  e.dir ∈ kc2_dirSet := by
-- proof
  apply StatMech.Walls.kc2_dart_dir_mem_dirSet e

/--
[kc2_dart_dir_rec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_dart_dir_rec_eq
  {P : Prop}
  {e : Dart}
-- given
  (h0 : e.dir = ![1, 0] → P)
  (h1 : e.dir = ![-1, 0] → P)
  (h2 : e.dir = ![0, 1] → P)
  (h3 : e.dir = ![0, -1] → P) :
-- imply
  P := by
-- proof
  apply StatMech.Walls.kc2_dart_dir_rec e h0 h1 h2 h3

/--
[kc2_orbit_dart_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_orbit_dart_iterate_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {b : {e : Dart // IsBoundaryDart K e}}
-- given
  (hb : b ∈ (dartOrbitWalk K a).support) :
-- imply
  ∃ k, (dartNextSub K)^[k] a = b := by
-- proof
  apply StatMech.Walls.kc2_orbit_dart_iterate K a hb

/--
[kc2_orbit_dir_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_orbit_dir_cases_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {b : {e : Dart // IsBoundaryDart K e}}
-- given
  (_hb : b ∈ (dartOrbitWalk K a).support) :
-- imply
  b.1.dir = ![1, 0] ∨ b.1.dir = ![-1, 0] ∨ b.1.dir = ![0, 1] ∨ b.1.dir = ![0, -1] := by
-- proof
  apply StatMech.Walls.kc2_orbit_dir_cases K a _hb

/--
[kc2_orbit_dir_mem_dirSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_orbit_dir_mem_dirSet_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {b : {e : Dart // IsBoundaryDart K e}}
-- given
  (_hb : b ∈ (dartOrbitWalk K a).support) :
-- imply
  b.1.dir ∈ kc2_dirSet := by
-- proof
  apply StatMech.Walls.kc2_orbit_dir_mem_dirSet K a _hb

/--
[kc2_orbit_dir_rec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_orbit_dir_rec_eq
  {P : Prop}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {b : {e : Dart // IsBoundaryDart K e}}
-- given
  (hb : b ∈ (dartOrbitWalk K a).support)
  (h0 : b.1.dir = ![1, 0] → P)
  (h1 : b.1.dir = ![-1, 0] → P)
  (h2 : b.1.dir = ![0, 1] → P)
  (h3 : b.1.dir = ![0, -1] → P) :
-- imply
  P := by
-- proof
  apply StatMech.Walls.kc2_orbit_dir_rec K a hb h0 h1 h2 h3

/--
[kc2_mkDart_dir_cardinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_dartdircases.lean)
-/
@[path]
private lemma kc2_mkDart_dir_cardinal_eq :
-- imply
  (mkDart 0 (![1, 0] : Site 2) kc2_unitWt_cardinal.1).dir = ![1, 0] := by
-- proof
  apply StatMech.Walls.kc2_mkDart_dir_cardinal


-- created on 2026-10-23
