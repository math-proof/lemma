import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive.Part3
open SimpleGraph StatMech StatMech.Universality


/--
[isingRectanglePrimitiveWithBase_eq_of_local_increments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma isingRectanglePrimitiveWithBase_eq_of_local_increments_eq
  {base : Real}
-- given
  (horizontal vertical G : Nat → Nat → Real)
  (width height : Nat)
  (hbase : G 0 0 = base)
  (hhorizontal : ∀ i < width, G (i + 1) 0 - G i 0 = horizontal i 0)
  (hvertical : ∀ i ≤ width, ∀ j < height, G i (j + 1) - G i j = vertical i j) :
-- imply
  ∀ i ≤ width, ∀ j ≤ height, G i j = base + isingRectanglePrimitive horizontal vertical i j := by
-- proof
  apply StatMech.Universality.isingRectanglePrimitiveWithBase_eq_of_local_increments base horizontal vertical G width height hbase hhorizontal hvertical

/--
[fkIsingSquareRadialPatchHorizontal_endpoint_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchHorizontal_endpoint_of_even_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i + 1 < m)
  (hj : j < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareInteriorRadialEndpoint n hn (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j) = fkIsingSquareRadialPatchPrimalFullVertex n m hm ⟨(⟨i, by omega⟩, ⟨j, hj⟩), heven⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchHorizontal_endpoint_of_even n m hn hm hmpos i j hi hj heven

/--
[fkIsingSquareRadialPatchHorizontal_face_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchHorizontal_face_of_even_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i + 1 < m)
  (hj : j < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j) = fkIsingSquareRadialPatchDualFullFace n m hm (by omega) ⟨(⟨i + 1, hi⟩, ⟨j, hj⟩), by change ¬ Even ((i + 1) + j) rw [Nat.not_even_iff] have hmod := Nat.even_iff.mp heven omega⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchHorizontal_face_of_even n m hn hm hmpos i j hi hj heven

/--
[fkIsingSquareRadialPatchHorizontal_endpoint_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchHorizontal_endpoint_of_odd_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i + 1 < m)
  (hj : j < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  fkIsingSquareInteriorRadialEndpoint n hn (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j) = fkIsingSquareRadialPatchPrimalFullVertex n m hm ⟨(⟨i + 1, hi⟩, ⟨j, hj⟩), by change Even ((i + 1) + j) rw [Nat.even_iff] have hmod := Nat.not_even_iff.mp hodd omega⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchHorizontal_endpoint_of_odd n m hn hm hmpos i j hi hj hodd

/--
[fkIsingSquareRadialPatchHorizontal_face_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchHorizontal_face_of_odd_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i + 1 < m)
  (hj : j < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j) = fkIsingSquareRadialPatchDualFullFace n m hm (by omega) ⟨(⟨i, by omega⟩, ⟨j, hj⟩), hodd⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchHorizontal_face_of_odd n m hn hm hmpos i j hi hj hodd

/--
[fkIsingSquareRadialPatchVertical_endpoint_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVertical_endpoint_of_even_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareInteriorRadialEndpoint n hn (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j) = fkIsingSquareRadialPatchPrimalFullVertex n m hm ⟨(⟨i, hi⟩, ⟨j, by omega⟩), heven⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVertical_endpoint_of_even n m hn hm hmpos i j hi hj heven

/--
[fkIsingSquareRadialPatchVertical_face_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVertical_face_of_even_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j) = fkIsingSquareRadialPatchDualFullFace n m hm (by omega) ⟨(⟨i, hi⟩, ⟨j + 1, hj⟩), by change ¬ Even (i + (j + 1)) rw [Nat.not_even_iff] have hmod := Nat.even_iff.mp heven omega⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVertical_face_of_even n m hn hm hmpos i j hi hj heven

/--
[fkIsingSquareRadialPatchVertical_endpoint_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVertical_endpoint_of_odd_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  fkIsingSquareInteriorRadialEndpoint n hn (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j) = fkIsingSquareRadialPatchPrimalFullVertex n m hm ⟨(⟨i, hi⟩, ⟨j + 1, hj⟩), by change Even (i + (j + 1)) rw [Nat.even_iff] have hmod := Nat.not_even_iff.mp hodd omega⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVertical_endpoint_of_odd n m hn hm hmpos i j hi hj hodd

/--
[fkIsingSquareRadialPatchVertical_face_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVertical_face_of_odd_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j) = fkIsingSquareRadialPatchDualFullFace n m hm (by omega) ⟨(⟨i, hi⟩, ⟨j, by omega⟩), hodd⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVertical_face_of_odd n m hn hm hmpos i j hi hj hodd

/--
[fkIsingSquareRadialPatchFullValue_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullValue_horizontal_increment_eq
  {n m : Nat}
  {vertexH : FKIsingSquareFullVertexNode n → Real}
  {faceH : FKIsingSquareFullFaceNode n → Real}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
  (hi : i + 1 < m)
  (hj : j < m) :
-- imply
  fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH ⟨i + 1, hi⟩ ⟨j, hj⟩ - fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH ⟨i, by omega⟩ ⟨j, hj⟩ = fkIsingSquareRadialPatchHorizontalSignedIncrement n m hn hm (by omega) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullValue_horizontal_increment n m hn hm hm2 vertexH faceH hcompatible i j hi hj

/--
[fkIsingSquareRadialPatchFullValue_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullValue_vertical_increment_eq
  {n m : Nat}
  {vertexH : FKIsingSquareFullVertexNode n → Real}
  {faceH : FKIsingSquareFullFaceNode n → Real}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
  (hi : i < m)
  (hj : j + 1 < m) :
-- imply
  fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH ⟨i, hi⟩ ⟨j + 1, hj⟩ - fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH ⟨i, hi⟩ ⟨j, by omega⟩ = fkIsingSquareRadialPatchVerticalSignedIncrement n m hn hm (by omega) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullValue_vertical_increment n m hn hm hm2 vertexH faceH hcompatible i j hi hj

/--
[fkIsingSquareRadialPatchFullValue_eq_primitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullValue_eq_primitive_eq
  {n m : Nat}
  {base : Real}
  {vertexH : FKIsingSquareFullVertexNode n → Real}
  {faceH : FKIsingSquareFullFaceNode n → Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
  (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
-- imply
  ∀ i j : Fin m, fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH i j = base + fkIsingSquareRadialPatchPrimitive n m hn hm (by omega) i.1 j.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullValue_eq_primitive n m hn hm hm2 base vertexH faceH hcompatible hbase

/--
[fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible_eq
  {n m : Nat}
  {base : Real}
  {vertexH : FKIsingSquareFullVertexNode n → Real}
  {faceH : FKIsingSquareFullFaceNode n → Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
  (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
-- imply
  ∀ p : FKIsingSquareRadialPatchPrimalNode m, fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p = vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible n m hn hm hm2 base vertexH faceH hcompatible hbase

/--
[fkIsingSquareRadialPatchDualValue_eq_full_of_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualValue_eq_full_of_compatible_eq
  {n m : Nat}
  {base : Real}
  {vertexH : FKIsingSquareFullVertexNode n → Real}
  {faceH : FKIsingSquareFullFaceNode n → Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
  (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
-- imply
  ∀ q : FKIsingSquareRadialPatchDualNode m, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q = faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualValue_eq_full_of_compatible n m hn hm hm2 base vertexH faceH hcompatible hbase

/--
[fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost_compatible_eq
  {n m : Nat}
  {base : Real}
  {vertexH : FKIsingSquareFullVertexNode n → Real}
  {faceH : FKIsingSquareFullFaceNode n → Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hvertexModified : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) vertexH x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - vertexH x) ≤ 0)
  (hvertexFixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexH x)
  (hfaceModified : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → 0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) faceH c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - faceH c))
  (hfaceFixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → faceH c ≤ 1)
  (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
  (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
-- imply
  (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ∧ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ≤ 1) ∧ (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ∧ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost_compatible n m hn hm hm2 base vertexH faceH hvertexModified hvertexFixed hfaceModified hfaceFixed hcompatible hbase


-- created on 2026-10-23
