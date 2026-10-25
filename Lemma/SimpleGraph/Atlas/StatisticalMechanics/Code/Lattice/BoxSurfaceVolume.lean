import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
open Set Finset Filter Topology StatMech StatMech.Lattice


/--
[boxSV_mem_boxF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_mem_boxF_eq
  {d n : ℕ}
  {x : Site d} :
-- imply
  x ∈ boxSV_boxF d n ↔ ∀ i, x i ∈ Finset.Icc (-(n : ℤ)) n := by
-- proof
  apply StatMech.Lattice.boxSV_mem_boxF

/--
[boxSV_coe_boxF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_coe_boxF_eq
  {d n : ℕ} :
-- imply
  ↑(boxSV_boxF d n) = box d n := by
-- proof
  apply StatMech.Lattice.boxSV_coe_boxF d n

/--
[boxSV_boxF_eq_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_boxF_eq_toFinset_eq
  {d n : ℕ} :
-- imply
  boxSV_boxF d n = (box_finite d n).toFinset := by
-- proof
  apply StatMech.Lattice.boxSV_boxF_eq_toFinset d n

/--
[boxSV_card_boxF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_card_boxF_eq
  {d n : ℕ} :
-- imply
  (boxSV_boxF d n).card = (2 * n + 1) ^ d := by
-- proof
  apply StatMech.Lattice.boxSV_card_boxF d n

/--
[boxSV_boxF_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_boxF_subset_eq
  {d : ℕ}
  {m n : ℕ}
-- given
  (h : m ≤ n) :
-- imply
  boxSV_boxF d m ⊆ boxSV_boxF d n := by
-- proof
  apply StatMech.Lattice.boxSV_boxF_subset d h

/--
[boxSV_coe_vbF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_coe_vbF_eq
  {d n : ℕ} :
-- imply
  ↑(boxSV_vbF d n) = vertexBoundary d n := by
-- proof
  apply StatMech.Lattice.boxSV_coe_vbF d n

/--
[boxSV_vbF_eq_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_vbF_eq_toFinset_eq
  {d n : ℕ} :
-- imply
  boxSV_vbF d n = (vertexBoundary_finite d n).toFinset := by
-- proof
  apply StatMech.Lattice.boxSV_vbF_eq_toFinset d n

/--
[boxSV_boundary_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_boundary_card_eq
  {d n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  boxSV_boundaryCard d n = (2 * n + 1) ^ d - (2 * n - 1) ^ d := by
-- proof
  apply StatMech.Lattice.boxSV_boundary_card d n hn

/--
[boxSV_mem_edgeF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_mem_edgeF_eq
  {d n : ℕ}
  {p : Site d × Site d} :
-- imply
  p ∈ boxSV_edgeF d n ↔ p.1 ∈ boxSV_boxF d n ∧ p.2 ∈ boxSV_boxF d n ∧ (hypercubicLattice d).Adj p.1 p.2 := by
-- proof
  apply StatMech.Lattice.boxSV_mem_edgeF

/--
[boxSV_fwd_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_fwd_adj_eq
  {d : ℕ}
  {x : Site d}
-- given
  (hd : 1 ≤ d) :
-- imply
  (hypercubicLattice d).Adj x (Function.update x ⟨0, hd⟩ (x ⟨0, hd⟩ + 1)) := by
-- proof
  apply StatMech.Lattice.boxSV_fwd_adj hd x

/--
[boxSV_fwd_maps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_fwd_maps_eq
  {d n : ℕ}
  {x : Site d}
-- given
  (hd : 1 ≤ d)
  (hx : x ∈ boxSV_fwdDom d n hd) :
-- imply
  (x, Function.update x ⟨0, hd⟩ (x ⟨0, hd⟩ + 1)) ∈ boxSV_edgeF d n := by
-- proof
  apply StatMech.Lattice.boxSV_fwd_maps hd x hx

/--
[boxSV_card_fwdDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_card_fwdDom_eq
  {d n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (boxSV_fwdDom d n hd).card = (2 * n) * (2 * n + 1) ^ (d - 1) := by
-- proof
  apply StatMech.Lattice.boxSV_card_fwdDom hd

/--
[boxSV_edge_card_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_edge_card_lower_eq
  {d n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (2 * n) * (2 * n + 1) ^ (d - 1) ≤ boxSV_edgeCard d n := by
-- proof
  apply StatMech.Lattice.boxSV_edge_card_lower hd

/--
[boxSV_pow_sub_pow_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_pow_sub_pow_le_eq
  {a b : ℝ}
  {d : ℕ}
-- given
  (ha : 0 ≤ b)
  (hab : b ≤ a) :
-- imply
  a ^ d - b ^ d ≤ (a - b) * (d * a ^ (d - 1)) := by
-- proof
  apply StatMech.Lattice.boxSV_pow_sub_pow_le a b ha hab d

/--
[boxSV_ratio_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_ratio_le_eq
  {d n : ℕ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  (boxSV_boundaryCard d n : ℝ) / (boxSV_edgeCard d n : ℝ) ≤ (d : ℝ) / n := by
-- proof
  apply StatMech.Lattice.boxSV_ratio_le d n hd hn

/--
[boxSV_ratio_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_ratio_tendsto_zero_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => (boxSV_boundaryCard d n : ℝ) / (boxSV_edgeCard d n : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Lattice.boxSV_ratio_tendsto_zero d hd

/--
[boxSV_edge_card_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean)
-/
@[path]
private lemma boxSV_edge_card_tendsto_atTop_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => boxSV_edgeCard d n) atTop atTop := by
-- proof
  apply StatMech.Lattice.boxSV_edge_card_tendsto_atTop d hd


-- created on 2026-10-23
