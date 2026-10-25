import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidenceFiber
open StatMech StatMech.Universality


/--
[fkIsingSquareInteriorRadialDart_eq_or_bondMate_of_endpoint_faceKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidenceFiber.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialDart_eq_or_bondMate_of_endpoint_faceKey_eq
  {n : Nat}
  {d f : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n)
  (hend : fkIsingSquareDartEndpoint n d.1 = fkIsingSquareDartEndpoint n f.1)
  (hface : fkIsingSquareWedgeFaceKey n d.1 = fkIsingSquareWedgeFaceKey n f.1) :
-- imply
  d.1 = f.1 ∨ fkIsingSquareBondMate n hn d.1 = f.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialDart_eq_or_bondMate_of_endpoint_faceKey n hn d f hend hface

/--
[fkIsingSquareInteriorRadialIncidence_ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidenceFiber.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialIncidence_ext_eq
  {n : Nat}
  {e f : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n)
  (hend : fkIsingSquareInteriorRadialEndpoint n hn e = fkIsingSquareInteriorRadialEndpoint n hn f)
  (hface : fkIsingSquareInteriorRadialFaceKey n hn e = fkIsingSquareInteriorRadialFaceKey n hn f) :
-- imply
  e = f := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialIncidence_ext n hn e f hend hface

/--
[fkIsingSquareInteriorRadial_endpoint_faceKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidenceFiber.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadial_endpoint_faceKey_injective_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Injective (fun e : FKIsingSquareInteriorRadialIncidence n hn ↦ (fkIsingSquareInteriorRadialEndpoint n hn e, fkIsingSquareInteriorRadialFaceKey n hn e)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadial_endpoint_faceKey_injective n hn


-- created on 2026-10-23
