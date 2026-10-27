import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc2_supportisface
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc2_mpl_orbitLoop_support_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_supportisface.lean)
-/
@[path]
private lemma kc2_mpl_orbitLoop_support_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitLoop K a).support = (List.range (dartOrbitPeriod K a + 1)).map (fun k => dartFace ((dartNext K)^[k] a.1)) := by
-- proof
  apply StatMech.Walls.kc2_mpl_orbitLoop_support_eq K a

/--
[kc2_support_is_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_supportisface.lean)
-/
@[path]
private lemma kc2_support_is_face_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hz : z ∈ (mpl_orbitLoop K a).support) :
-- imply
  ∃ i ≤ dartOrbitPeriod K a, z = dartFace ((dartNext K)^[i] a.1) ∧ IsBoundaryDart K ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Walls.kc2_support_is_face K a hz

/--
[kc2_support_is_face_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_supportisface.lean)
-/
@[path]
private lemma kc2_support_is_face_exists_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hz : z ∈ (mpl_orbitLoop K a).support) :
-- imply
  ∃ i, z = dartFace ((dartNext K)^[i] a.1) ∧ IsBoundaryDart K ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Walls.kc2_support_is_face_exists K a hz

/--
[kc2_dartFace_iterate_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_supportisface.lean)
-/
@[path]
private lemma kc2_dartFace_iterate_mem_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ}
-- given
  (hK : K.Finite) :
-- imply
  dartFace ((dartNext K)^[n] a.1) ∈ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Walls.kc2_dartFace_iterate_mem_support K hK a n

/--
[kc2_support_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_supportisface.lean)
-/
@[path]
private lemma kc2_support_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite) :
-- imply
  z ∈ (mpl_orbitLoop K a).support ↔ ∃ i, z = dartFace ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Walls.kc2_support_iff K hK a

/--
[kc2_base_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_supportisface.lean)
-/
@[path]
private lemma kc2_base_mem_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  dartFace a.1 ∈ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Walls.kc2_base_mem_support K a


-- created on 2026-10-23
