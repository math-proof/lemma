import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FKGeneralQConnectionFKG
open MeasureTheory Set Filter Topology StatMech StatMech.FK


/--
[fkg_iUnion_of_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConnectionFKG.lean)
-/
@[path]
private lemma fkg_iUnion_of_monotone_eq
  [Countable E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
-- given
  (A B : Nat -> Set (ConfigSpace E))
  (hAmono : Monotone A)
  (hBmono : Monotone B)
  (hstage : forall n, mu.real (A n) * mu.real (B n) <= mu.real (A n ∩ B n)) :
-- imply
  mu.real (⋃ n, A n) * mu.real (⋃ n, B n) <= mu.real ((⋃ n, A n) ∩ (⋃ n, B n)) := by
-- proof
  apply StatMech.FK.fkg_iUnion_of_monotone mu A B hAmono hBmono hstage

/--
[connectedWithinBox_eq_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConnectionFKG.lean)
-/
@[path]
private lemma connectedWithinBox_eq_boxConnEvent_eq
  {d : Nat}
  {x y : Site d}
  {n : Nat}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  zbd_connectedWithinBox x y n = boxConnEvent d n (⟨x, hx⟩ : boxVerts d n) ⟨y, hy⟩ := by
-- proof
  apply StatMech.FK.connectedWithinBox_eq_boxConnEvent hx hy

/--
[fkgq_freeInfiniteVolume_boxConnEvent_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConnectionFKG.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_boxConnEvent_pos_eq
  {d : Nat}
  {p q : Real}
  {n : Nat}
  {x y : boxVerts d n}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  0 < (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxConnEvent d n x y) := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_boxConnEvent_pos hp hp1 hq n x y

/--
[fkgq_freeInfiniteVolume_connection_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConnectionFKG.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_connection_pos_eq
  {d : Nat}
  {p q : Real}
  {x y : Site d}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  0 < (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real {omega | StatMech.Lattice.Connected d omega x y} := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_connection_pos hp hp1 hq x y

/--
[fkgq_freeInfiniteVolume_connectedWithinBox_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConnectionFKG.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_connectedWithinBox_fkg_eq
  {d : Nat}
  {p q : Real}
  {x y u v : Site d}
  {n : Nat}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) mu.real (zbd_connectedWithinBox x y n) * mu.real (zbd_connectedWithinBox u v n) <= mu.real (zbd_connectedWithinBox x y n ∩ zbd_connectedWithinBox u v n) := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_connectedWithinBox_fkg hp hp1 hq x y u v n

/--
[fkgq_freeInfiniteVolume_connection_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConnectionFKG.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_connection_fkg_eq
  {d : Nat}
  {p q : Real}
  {x y u v : Site d}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) mu.real {omega | StatMech.Lattice.Connected d omega x y} * mu.real {omega | StatMech.Lattice.Connected d omega u v} <= mu.real ({omega | StatMech.Lattice.Connected d omega x y} ∩ {omega | StatMech.Lattice.Connected d omega u v}) := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_connection_fkg hp hp1 hq x y u v


-- created on 2026-10-23
