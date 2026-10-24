import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost
open SimpleGraph StatMech StatMech.Universality


/--
[fkIsingSquareFullFaceOfKey_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareFullFaceOfKey_key_eq
  {n : Nat}
  {p : Int × Int}
-- given
  (hp : fkIsingSquareInteriorFaceKey n p) :
-- imply
  fkIsingSquareInteriorCellKey n (fkIsingSquareFullFaceOfKey n p hp) = p := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullFaceOfKey_key n p hp

/--
[fkIsingSquareFullFaceOfRadialIncidence_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareFullFaceOfRadialIncidence_key_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorCellKey n (fkIsingSquareFullFaceOfRadialIncidence n hn e) = fkIsingSquareInteriorRadialFaceKey n hn e := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullFaceOfRadialIncidence_key n hn e

/--
[fkIsingSquareFullVertexGhostMultiplicity_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareFullVertexGhostMultiplicity_pos_iff_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  0 < fkIsingSquareFullVertexGhostMultiplicity n x ↔ x.1 1 = -(n : Int) ∨ x.1 0 = (n : Int) ∨ x.1 1 = (n : Int) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullVertexGhostMultiplicity_pos_iff n x

/--
[fkIsingSquareFullFaceGhostMultiplicity_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareFullFaceGhostMultiplicity_pos_iff_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  0 < fkIsingSquareFullFaceGhostMultiplicity n c ↔ c.1.1 = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullFaceGhostMultiplicity_pos_iff n c

/--
[fkIsingSquareFullVertex_boundary_fixed_or_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareFullVertex_boundary_fixed_or_ghost_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hx : fkIsingSquareBoxBoundary n x) :
-- imply
  fkIsingSquareFullVertexFixedBoundary n x ∨ 0 < fkIsingSquareFullVertexGhostMultiplicity n x := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullVertex_boundary_fixed_or_ghost n x hx

/--
[fkIsingSquareFullVertex_reaches_fixed_or_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareFullVertex_reaches_fixed_or_ghost_eq
  {n : Nat} :
-- imply
  ∀ x : FKIsingSquareFullVertexNode n, ∃ b, (fkIsingSquareFullVertexFixedBoundary n b ∨ 0 < fkIsingSquareFullVertexGhostMultiplicity n b) ∧ (fkIsingSquareFullVertexGraph n).Reachable x b := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullVertex_reaches_fixed_or_ghost n

/--
[fkIsingSquareFullFace_reaches_fixed_or_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareFullFace_reaches_fixed_or_ghost_eq
  {n : Nat} :
-- imply
  ∀ c : FKIsingSquareFullFaceNode n, ∃ b, (fkIsingSquareFullFaceFixedBoundary n b ∨ 0 < fkIsingSquareFullFaceGhostMultiplicity n b) ∧ (fkIsingSquareFullFaceGraph n).Reachable c b := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullFace_reaches_fixed_or_ghost n

/--
[fkIsingSquareFullVertex_zero_le_of_modifiedSuperharmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareFullVertex_zero_le_of_modifiedSuperharmonic_eq
  {n : Nat}
  {H : FKIsingSquareFullVertexNode n → Real}
-- given
  (hmodified : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) H x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - H x) ≤ 0)
  (hfixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ H x) :
-- imply
  ∀ x, 0 ≤ H x := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullVertex_zero_le_of_modifiedSuperharmonic n H hmodified hfixed

/--
[fkIsingSquareFullFace_le_one_of_modifiedSubharmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareFullFace_le_one_of_modifiedSubharmonic_eq
  {n : Nat}
  {H : FKIsingSquareFullFaceNode n → Real}
-- given
  (hmodified : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → 0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - H c))
  (hfixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → H c ≤ 1) :
-- imply
  ∀ c, H c ≤ 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullFace_le_one_of_modifiedSubharmonic n H hmodified hfixed

/--
[fkIsingSquareRadialPatchDualFullFace_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualFullFace_key_eq
  {n m : Nat}
  {q : FKIsingSquareRadialPatchDualNode m}
-- given
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  fkIsingSquareInteriorCellKey n (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) = (((q.1.1.1 + q.1.2.1 + 1) / 2 : Int) - 1, (q.1.1.1 : Int) - ((q.1.1.1 + q.1.2.1 + 1) / 2 : Int)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualFullFace_key n m hm hm2 q

/--
[fkIsingSquareRadialPatchDualFullFace_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualFullFace_injective_eq
  {n m : Nat}
-- given
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  Function.Injective (fkIsingSquareRadialPatchDualFullFace n m hm hm2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualFullFace_injective n m hm hm2

/--
[fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost_eq
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
  (hprimalRestriction : ∀ p, fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p = vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p))
  (hdualRestriction : ∀ q, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q = faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q)) :
-- imply
  (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ∧ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ≤ 1) ∧ (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ∧ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost n m hn hm hm2 base vertexH faceH hvertexModified hvertexFixed hfaceModified hfaceFixed hprimalRestriction hdualRestriction


-- created on 2026-10-23
