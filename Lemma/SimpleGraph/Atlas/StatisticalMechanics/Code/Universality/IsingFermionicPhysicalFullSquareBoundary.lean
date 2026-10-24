import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundary
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareFullIntegratedPrimitive


/--
[fkIsingSquareWired_terminalBond_mem_explorationOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma fkIsingSquareWired_terminalBond_mem_explorationOrder_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (.bond (fkIsingSquareWiredTerminalDart n hn) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_terminalBond_mem_explorationOrder n hn omega

/--
[fkIsingSquareWired_terminalBond_rawTurnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma fkIsingSquareWired_terminalBond_rawTurnCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn omega (.bond (fkIsingSquareWiredTerminalDart n hn)) = fkIsingSquareWiredRawTurnCount n hn omega .terminal := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_terminalBond_rawTurnCount n hn omega

/--
[fkIsingSquareWired_terminalBond_observable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma fkIsingSquareWired_terminalBond_observable_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.bond (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_terminalBond_observable n hn

/--
[fkIsingSquareWired_terminalDart_observable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma fkIsingSquareWired_terminalDart_observable_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_terminalDart_observable n hn

/--
[fkIsingSquareWired_terminalDart_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma fkIsingSquareWired_terminalDart_increment_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_terminalDart_increment n hn

/--
[vertex_eq_of_common_face_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma vertex_eq_of_common_face_increment_eq_eq
  {n : Nat}
  {e f : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n)
  (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e = fkIsingSquareFullFaceOfRadialIncidence n hn f)
  (hinc : fkIsingSquareInteriorRadialIncrement n hn e = fkIsingSquareInteriorRadialIncrement n hn f) :
-- imply
  vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) = vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn f) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.vertex_eq_of_common_face_increment_eq n hn e f hface hinc

/--
[face_eq_of_common_vertex_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma face_eq_of_common_vertex_increment_eq_eq
  {n : Nat}
  {e f : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n)
  (hvertex : fkIsingSquareInteriorRadialEndpoint n hn e = fkIsingSquareInteriorRadialEndpoint n hn f)
  (hinc : fkIsingSquareInteriorRadialIncrement n hn e = fkIsingSquareInteriorRadialIncrement n hn f) :
-- imply
  facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn e) = facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn f) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.face_eq_of_common_vertex_increment_eq n hn e f hvertex hinc

/--
[left_boundary_interior_increment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma left_boundary_interior_increment_eq_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorRadialIncrement n hn (Quot.mk _ (leftInteriorEastDart n hn k)) = fkIsingSquareInteriorRadialIncrement n hn (Quot.mk _ (leftInteriorSouthDart n hn k)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.left_boundary_interior_increment_eq n hn k

/--
[wiredArc_vertex_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma wiredArc_vertex_step_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  vertexPrimitive n hn (fkIsingSquareLeftVerticalLower n hn k) = vertexPrimitive n hn (fkIsingSquareLeftVerticalUpper n hn k) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.wiredArc_vertex_step n hn k

/--
[vertex_fixedBoundary_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma vertex_fixedBoundary_eq_zero_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hx : fkIsingSquareFullVertexFixedBoundary n x) :
-- imply
  vertexPrimitive n hn x = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.vertex_fixedBoundary_eq_zero n hn x hx

/--
[vertex_fixedBoundary_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma vertex_fixedBoundary_nonneg_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hx : fkIsingSquareFullVertexFixedBoundary n x) :
-- imply
  0 ≤ vertexPrimitive n hn x := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.vertex_fixedBoundary_nonneg n hn x hx

/--
[terminalAdjacentFace_fixedBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma terminalAdjacentFace_fixedBoundary_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareFullFaceFixedBoundary n (terminalAdjacentFace n hn) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace_fixedBoundary n hn

/--
[terminalAdjacentFace_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean)
-/
@[path]
private lemma terminalAdjacentFace_le_one_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  facePrimitive n hn (terminalAdjacentFace n hn) ≤ 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace_le_one n hn


-- created on 2026-10-23
