import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.EulerFaces
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[mem_hEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma mem_hEdges_eq
  {n : ℕ}
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ hEdges n ↔ ∃ a b : ℤ, -(n : ℤ) ≤ a ∧ a < n ∧ -(n : ℤ) ≤ b ∧ b ≤ n ∧ e = s(![a, b], ![a + 1, b]) := by
-- proof
  apply StatMech.Lattice.mem_hEdges

/--
[mem_vEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma mem_vEdges_eq
  {n : ℕ}
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ vEdges n ↔ ∃ a b : ℤ, -(n : ℤ) ≤ a ∧ a ≤ n ∧ -(n : ℤ) ≤ b ∧ b < n ∧ e = s(![a, b], ![a, b + 1]) := by
-- proof
  apply StatMech.Lattice.mem_vEdges

/--
[mem_box2'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma mem_box2'_eq
  {n : ℕ}
  {x : Site 2} :
-- imply
  x ∈ box 2 n ↔ (x 0).natAbs ≤ n ∧ (x 1).natAbs ≤ n := by
-- proof
  apply StatMech.Lattice.mem_box2'

/--
[adj_box_mem_boxEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma adj_box_mem_boxEdges_eq
  {n : ℕ}
  {x y : Site 2}
-- given
  (hx : x ∈ box 2 n)
  (hy : y ∈ box 2 n)
  (hadj : (hypercubicLattice 2).Adj x y) :
-- imply
  s(x, y) ∈ boxEdges n := by
-- proof
  apply StatMech.Lattice.adj_box_mem_boxEdges n hx hy hadj

/--
[mem_boxEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma mem_boxEdges_iff_eq
  {n : ℕ}
  {x y : Site 2} :
-- imply
  s(x, y) ∈ boxEdges n ↔ x ∈ box 2 n ∧ y ∈ box 2 n ∧ (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.Lattice.mem_boxEdges_iff n x y

/--
[icc_card_n](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma icc_card_n_eq
  {n : ℕ} :
-- imply
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
-- proof
  apply StatMech.Lattice.icc_card_n n

/--
[ico_card_n](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma ico_card_n_eq
  {n : ℕ} :
-- imply
  (Finset.Ico (-(n : ℤ)) (n : ℤ)).card = 2 * n := by
-- proof
  apply StatMech.Lattice.ico_card_n n

/--
[boxVerts_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma boxVerts_card_eq
  {n : ℕ} :
-- imply
  (boxVerts n).card = (2 * n + 1) ^ 2 := by
-- proof
  apply StatMech.Lattice.boxVerts_card n

/--
[hEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma hEdges_card_eq
  {n : ℕ} :
-- imply
  (hEdges n).card = (2 * n) * (2 * n + 1) := by
-- proof
  apply StatMech.Lattice.hEdges_card n

/--
[vEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma vEdges_card_eq
  {n : ℕ} :
-- imply
  (vEdges n).card = (2 * n + 1) * (2 * n) := by
-- proof
  apply StatMech.Lattice.vEdges_card n

/--
[hEdges_disjoint_vEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma hEdges_disjoint_vEdges_eq
  {n : ℕ} :
-- imply
  Disjoint (hEdges n) (vEdges n) := by
-- proof
  apply StatMech.Lattice.hEdges_disjoint_vEdges n

/--
[boxEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma boxEdges_card_eq
  {n : ℕ} :
-- imply
  (boxEdges n).card = 2 * ((2 * n) * (2 * n + 1)) := by
-- proof
  apply StatMech.Lattice.boxEdges_card n

/--
[boxCells_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma boxCells_card_eq
  {n : ℕ} :
-- imply
  (boxCells n).card = (2 * n) ^ 2 := by
-- proof
  apply StatMech.Lattice.boxCells_card n

/--
[boxFaceCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma boxFaceCount_eq_eq
  {n : ℕ} :
-- imply
  boxFaceCount n = (2 * n) ^ 2 + 1 := by
-- proof
  apply StatMech.Lattice.boxFaceCount_eq n

/--
[box_euler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma box_euler_eq
  {n : ℕ} :
-- imply
  (boxVerts n).card + boxFaceCount n = (boxEdges n).card + 2 := by
-- proof
  apply StatMech.Lattice.box_euler n

/--
[box_euler_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma box_euler_sub_eq
  {n : ℕ} :
-- imply
  ((boxVerts n).card : ℤ) - (boxEdges n).card + boxFaceCount n = 2 := by
-- proof
  apply StatMech.Lattice.box_euler_sub n

/--
[box_faceCount_eq_cyclomatic_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma box_faceCount_eq_cyclomatic_add_one_eq
  {n : ℕ} :
-- imply
  boxFaceCount n = (((boxEdges n).card + 1) - (boxVerts n).card) + 1 := by
-- proof
  apply StatMech.Lattice.box_faceCount_eq_cyclomatic_add_one n

/--
[mem_box2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma mem_box2_eq
  {n : ℕ}
  {a b : ℤ}
-- given
  (ha : a.natAbs ≤ n)
  (hb : b.natAbs ≤ n) :
-- imply
  (![a, b] : Site 2) ∈ box 2 n := by
-- proof
  apply StatMech.Lattice.mem_box2 ha hb

/--
[boxInduce_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma boxInduce_adj_eq
  {n : ℕ}
  {x y : Site 2}
-- given
  (hx : x ∈ box 2 n)
  (hy : y ∈ box 2 n)
  (hadj : (hypercubicLattice 2).Adj x y) :
-- imply
  (boxInduce n).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Lattice.boxInduce_adj hx hy hadj

/--
[hadj_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma hadj_step_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
-- proof
  apply StatMech.Lattice.hadj_step a b

/--
[vadj_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma vadj_step_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a, b + 1] := by
-- proof
  apply StatMech.Lattice.vadj_step a b

/--
[reach_to_zero0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma reach_to_zero0_eq
  {n : ℕ}
  {b : ℤ}
-- given
  (hb : b.natAbs ≤ n) :
-- imply
  ∀ a : ℤ, (ha : a.natAbs ≤ n) → (boxInduce n).Reachable ⟨![a, b], mem_box2 ha hb⟩ ⟨![0, b], mem_box2 (by simp) hb⟩ := by
-- proof
  apply StatMech.Lattice.reach_to_zero0 b hb

/--
[reach_to_zero1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma reach_to_zero1_eq
  {n : ℕ}
  {a : ℤ}
-- given
  (ha : a.natAbs ≤ n) :
-- imply
  ∀ b : ℤ, (hb : b.natAbs ≤ n) → (boxInduce n).Reachable ⟨![a, b], mem_box2 ha hb⟩ ⟨![a, 0], mem_box2 ha (by simp)⟩ := by
-- proof
  apply StatMech.Lattice.reach_to_zero1 a ha

/--
[reach_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma reach_origin_eq
  {n : ℕ}
  {a b : ℤ}
-- given
  (ha : a.natAbs ≤ n)
  (hb : b.natAbs ≤ n) :
-- imply
  (boxInduce n).Reachable ⟨![a, b], mem_box2 ha hb⟩ ⟨![0, 0], mem_box2 (by simp) (by simp)⟩ := by
-- proof
  apply StatMech.Lattice.reach_origin ha hb

/--
[boxInduce_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma boxInduce_connected_eq
  {n : ℕ} :
-- imply
  (boxInduce n).Connected := by
-- proof
  apply StatMech.Lattice.boxInduce_connected n

/--
[box_general_face_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean)
-/
@[path]
private lemma box_general_face_residue_eq :
-- imply
  True := by
-- proof
  apply StatMech.Lattice.box_general_face_residue


-- created on 2026-10-23
