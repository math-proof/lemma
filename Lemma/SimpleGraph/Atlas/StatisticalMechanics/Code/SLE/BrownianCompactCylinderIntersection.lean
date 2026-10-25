import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianCompactCylinderIntersection.Part3
open MeasureTheory Set StatMech StatMech.SLE


/--
[nonempty_iInter_cylinder_of_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean)
-/
@[path]
private lemma nonempty_iInter_cylinder_of_compact_eq
-- given
  (I : Nat -> Finset Real)
  (S : forall n, Set (I n -> Real))
  (hcompact : forall n, IsCompact (S n))
  (hnonempty : forall n, (S n).Nonempty)
  (hanti : Antitone (fun n => (cylinder (I n) (S n) : Set (Real -> Real)))) :
-- imply
  (iInter (fun n => (cylinder (I n) (S n) : Set (Real -> Real)))).Nonempty := by
-- proof
  apply StatMech.SLE.nonempty_iInter_cylinder_of_compact I S hcompact hnonempty hanti

/--
[cylinderPrefixSupport_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean)
-/
@[path]
private lemma cylinderPrefixSupport_subset_eq
  {k n : Nat}
-- given
  (I : Nat -> Finset Real)
  (hkn : k <= n) :
-- imply
  I k <= cylinderPrefixSupport I n := by
-- proof
  apply StatMech.SLE.cylinderPrefixSupport_subset I hkn

/--
[cylinder_cylinderPrefixBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean)
-/
@[path]
private lemma cylinder_cylinderPrefixBase_eq
  {n : Nat}
-- given
  (I : Nat -> Finset Real)
  (L : forall k, Set (I k -> Real)) :
-- imply
  (cylinder (cylinderPrefixSupport I n) (cylinderPrefixBase I L n) : Set (Real -> Real)) = iInter (fun k => iInter (fun _hkn : k <= n => (cylinder (I k) (L k) : Set (Real -> Real)))) := by
-- proof
  apply StatMech.SLE.cylinder_cylinderPrefixBase I L n

/--
[cylinderPrefixBase_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean)
-/
@[path]
private lemma cylinderPrefixBase_isCompact_eq
  {n : Nat}
-- given
  (I : Nat -> Finset Real)
  (L : forall k, Set (I k -> Real))
  (hcompact : forall k, IsCompact (L k)) :
-- imply
  IsCompact (cylinderPrefixBase I L n) := by
-- proof
  apply StatMech.SLE.cylinderPrefixBase_isCompact I L hcompact n


-- created on 2026-10-23
