import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc39threereplica
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc39_sharpResidue_iff_allConn_ge_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean)
-/
@[path]
private lemma gc39_sharpResidue_iff_allConn_ge_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc38_SharpGHSResidue G β h o x y ↔ (gc15_Z0 G β h) ^ 2 * gc37_triple G β h o x y ≤ gc39_allConnSum G β h o x y := by
-- proof
  apply StatMech.Walls.gc39_sharpResidue_iff_allConn_ge_triple G β h hβ hh o x y hox hoy hxy

/--
[gc39_sharpResidue_of_csTriple_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean)
-/
@[path]
private lemma gc39_sharpResidue_of_csTriple_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hdom : gc39_csTriple G β h o x y ≤ gc15_Z0 G β h * gc39_allConnSum G β h o x y) :
-- imply
  gc38_SharpGHSResidue G β h o x y := by
-- proof
  apply StatMech.Walls.gc39_sharpResidue_of_csTriple_le G β h hβ hh o x y hox hoy hxy hdom

/--
[gc39_sharpResidue_of_improvedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean)
-/
@[path]
private lemma gc39_sharpResidue_of_improvedBound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hres : gc39_ThreeReplicaImprovedBound G β h o x y) :
-- imply
  gc38_SharpGHSResidue G β h o x y := by
-- proof
  apply StatMech.Walls.gc39_sharpResidue_of_improvedBound G β h hβ hh o x y hox hoy hxy hres

/--
[gc39_ursell3_nonpos_of_improvedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean)
-/
@[path]
private lemma gc39_ursell3_nonpos_of_improvedBound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hres : gc39_ThreeReplicaImprovedBound G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc39_ursell3_nonpos_of_improvedBound G β h hβ hh o x y hox hoy hxy hres

/--
[gc39_improvedBound_iff_sharpResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean)
-/
@[path]
private lemma gc39_improvedBound_iff_sharpResidue_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc39_ThreeReplicaImprovedBound G β h o x y ↔ gc38_SharpGHSResidue G β h o x y := by
-- proof
  apply StatMech.Walls.gc39_improvedBound_iff_sharpResidue G β h hβ hh o x y hox hoy hxy

/--
[gc39_improvedBound_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean)
-/
@[path]
private lemma gc39_improvedBound_at_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc39_ThreeReplicaImprovedBound G β 0 o x y := by
-- proof
  apply StatMech.Walls.gc39_improvedBound_at_zero G β hβ o x y hox hoy hxy

/--
[gc39_improvedBound_sides_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean)
-/
@[path]
private lemma gc39_improvedBound_sides_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ gc39_csTriple G β h o x y ∧ 0 ≤ gc15_Z0 G β h * gc39_allConnSum G β h o x y := by
-- proof
  apply StatMech.Walls.gc39_improvedBound_sides_nonneg G β h hβ hh o x y


-- created on 2026-10-23
