import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
open Set SimpleGraph StatMech StatMech.Lattice


/--
[boxMinusP_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma boxMinusP_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {u v : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d) :
-- imply
  (boxMinusP ω α β m m' c d xB hxB).Adj u v ↔ (hypercubicLattice 2).Adj u v ∧ u ∈ rect α β c d ∧ v ∈ rect α β c d ∧ u ∉ overlapComp ω m m' c d xB hxB ∧ v ∉ overlapComp ω m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.boxMinusP_adj ω α β m m' c d xB hxB u v

/--
[boxMinusP_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma boxMinusP_le_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d) :
-- imply
  boxMinusP ω α β m m' c d xB hxB ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.boxMinusP_le ω α β m m' c d xB hxB

/--
[boxMinusP_walk_dest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma boxMinusP_walk_dest_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {x z : Site 2}
  {w : (boxMinusP ω α β m m' c d xB hxB).Walk x z}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hx : x ∈ rect α β c d)
  (hxP : x ∉ overlapComp ω m m' c d xB hxB) :
-- imply
  z ∈ rect α β c d ∧ z ∉ overlapComp ω m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.boxMinusP_walk_dest ω α β m m' c d xB hxB hx hxP w

/--
[mem_arcS_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma mem_arcS_leftRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {z : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d) :
-- imply
  z ∈ arcS_leftRegion ω α β m m' c d xB hxB ↔ z ∈ rect α β c d ∧ (z 0 = α ∨ z ∈ floodFromLeft ω α β m m' c d xB hxB) := by
-- proof
  apply StatMech.Lattice.mem_arcS_leftRegion ω α β m m' c d xB hxB z

/--
[floodFromLeft_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma floodFromLeft_subset_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {z : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hz : z ∈ floodFromLeft ω α β m m' c d xB hxB) :
-- imply
  z ∈ rect α β c d ∧ z ∉ overlapComp ω m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.floodFromLeft_subset ω α β m m' c d xB hxB hz

/--
[arcS_leftRegion_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma arcS_leftRegion_subset_box_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {z : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hz : z ∈ arcS_leftRegion ω α β m m' c d xB hxB) :
-- imply
  z ∈ rect α β c d := by
-- proof
  apply StatMech.Lattice.arcS_leftRegion_subset_box ω α β m m' c d xB hxB hz

/--
[arcS_leftRegion_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma arcS_leftRegion_left_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {z : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hz : z ∈ rect α β c d)
  (hzα : z 0 = α) :
-- imply
  z ∈ arcS_leftRegion ω α β m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.arcS_leftRegion_left ω α β m m' c d xB hxB z hz hzα

/--
[flood_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma flood_step_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {w t : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hwL : w ∈ arcS_leftRegion ω α β m m' c d xB hxB)
  (hwP : w ∉ overlapComp ω m m' c d xB hxB)
  (hadj : (hypercubicLattice 2).Adj w t)
  (ht : t ∈ rect α β c d)
  (htP : t ∉ overlapComp ω m m' c d xB hxB) :
-- imply
  t ∈ floodFromLeft ω α β m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.flood_step ω α β m m' c d xB hxB hwL hwP hadj ht htP

/--
[arcS_leftRegion_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma arcS_leftRegion_bdEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {u v : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hu : u ∈ rect α β c d)
  (hv : v ∈ rect α β c d)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (arcS_leftRegion ω α β m m' c d xB hxB) s(u, v)) :
-- imply
  u ∈ overlapComp ω m m' c d xB hxB ∨ v ∈ overlapComp ω m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.arcS_leftRegion_bdEdge ω α β m m' c d xB hxB u v hu hv hadj hbd

/--
[arcS_rightWall_in_L_gives_avoiding_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma arcS_rightWall_in_L_gives_avoiding_walk_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {y : Site 2}
-- given
  (hαβ : α < β)
  (hxB : xB ∈ rect m m' c d)
  (_hy : y ∈ rect α β c d)
  (hyβ : y 0 = β)
  (hyL : y ∈ arcS_leftRegion ω α β m m' c d xB hxB) :
-- imply
  ∃ (x : Site 2) (γ : (hypercubicLattice 2).Walk x y), x ∈ rect α β c d ∧ x 0 = α ∧ (∀ z ∈ γ.support, z ∈ rect α β c d ∧ z ∉ overlapComp ω m m' c d xB hxB) := by
-- proof
  apply StatMech.Lattice.arcS_rightWall_in_L_gives_avoiding_walk ω hαβ xB hxB _hy hyβ hyL

/--
[arcS_leftRegion_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma arcS_leftRegion_right_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
  {xB : Site 2}
  {z : Site 2}
-- given
  (hαβ : α < β)
  (hαm : α ≤ m)
  (hmm' : m ≤ m')
  (hm'β : m' ≤ β)
  (hxB : xB ∈ rect m m' c d)
  (hcross : ArcS_TwoPathsCross ω α β m m' c d xB hxB)
  (hz : z ∈ rect α β c d)
  (hzβ : z 0 = β) :
-- imply
  z ∉ arcS_leftRegion ω α β m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.arcS_leftRegion_right ω hαβ hαm hmm' hm'β xB hxB hcross z hz hzβ

/--
[arcS_arc_sides_of_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean)
-/
@[path]
private lemma arcS_arc_sides_of_cross_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
-- given
  (hαβ : α < β)
  (hcross : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d), ArcS_TwoPathsCross ω α β m m' c d xB hxB) :
-- imply
  StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
-- proof
  apply StatMech.Lattice.arcS_arc_sides_of_cross ω hαβ hcross


-- created on 2026-10-23
