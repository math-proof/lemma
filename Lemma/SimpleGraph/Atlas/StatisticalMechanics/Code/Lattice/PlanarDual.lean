import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.PlanarDual
open SimpleGraph StatMech StatMech.Lattice


/--
[dualLattice_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma dualLattice_adj_eq
  {x y : Site 2} :
-- imply
  dualLattice.Adj x y ↔ (∑ i, (x i - y i).natAbs) = 1 := by
-- proof
  apply StatMech.Lattice.dualLattice_adj x y

/--
[rot90Fun_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma rot90Fun_apply_eq
  {a b : ℤ} :
-- imply
  rot90Fun ![a, b] = ![-b, a] := by
-- proof
  apply StatMech.Lattice.rot90Fun_apply a b

/--
[rot90Inv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma rot90Inv_apply_eq
  {a b : ℤ} :
-- imply
  rot90Inv ![a, b] = ![b, -a] := by
-- proof
  apply StatMech.Lattice.rot90Inv_apply a b

/--
[rot90Equiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma rot90Equiv_apply_eq
  {x : Site 2} :
-- imply
  rot90Equiv x = rot90Fun x := by
-- proof
  apply StatMech.Lattice.rot90Equiv_apply x

/--
[rot90Equiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma rot90Equiv_symm_apply_eq
  {x : Site 2} :
-- imply
  rot90Equiv.symm x = rot90Inv x := by
-- proof
  apply StatMech.Lattice.rot90Equiv_symm_apply x

/--
[rot90_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma rot90_adj_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj (rot90Fun x) (rot90Fun y) ↔ (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.Lattice.rot90_adj x y

/--
[rot90Iso_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma rot90Iso_apply_eq
  {x : Site 2} :
-- imply
  rot90Iso x = rot90Fun x := by
-- proof
  apply StatMech.Lattice.rot90Iso_apply x

/--
[selfDual_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma selfDual_apply_eq
  {x : Site 2} :
-- imply
  selfDual x = x := by
-- proof
  apply StatMech.Lattice.selfDual_apply x

/--
[selfDualCross_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma selfDualCross_apply_eq
  {x : Site 2} :
-- imply
  selfDualCross x = rot90Fun x := by
-- proof
  apply StatMech.Lattice.selfDualCross_apply x

/--
[crossingEdgeEquiv_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma crossingEdgeEquiv_coe_eq
  {e : (hypercubicLattice 2).edgeSet} :
-- imply
  (crossingEdgeEquiv e : Sym2 (Site 2)) = Sym2.map (⇑rot90Iso) e := by
-- proof
  apply StatMech.Lattice.crossingEdgeEquiv_coe e

/--
[crossingEdgeEquiv_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma crossingEdgeEquiv_horizontal_eq
  {a b : ℤ}
-- given
  (he : s(![a, b], ![a + 1, b]) ∈ (hypercubicLattice 2).edgeSet) :
-- imply
  (crossingEdgeEquiv ⟨_, he⟩ : Sym2 (Site 2)) = s(![-b, a], ![-b, a + 1]) := by
-- proof
  apply StatMech.Lattice.crossingEdgeEquiv_horizontal a b he

/--
[crossingEdgeEquiv_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma crossingEdgeEquiv_vertical_eq
  {a b : ℤ}
-- given
  (he : s(![a, b], ![a, b + 1]) ∈ (hypercubicLattice 2).edgeSet) :
-- imply
  (crossingEdgeEquiv ⟨_, he⟩ : Sym2 (Site 2)) = s(![-b, a], ![-(b + 1), a]) := by
-- proof
  apply StatMech.Lattice.crossingEdgeEquiv_vertical a b he

/--
[sym2Congr_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma sym2Congr_mk_eq
  {e : α ≃ β}
  {a b : α} :
-- imply
  sym2Congr e s(a, b) = s(e a, e b) := by
-- proof
  apply StatMech.Lattice.sym2Congr_mk e a b

/--
[crossEdge_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma crossEdge_mk_eq
  {x y : Site 2} :
-- imply
  crossEdge s(x, y) = s(rot90Fun x, rot90Fun y) := by
-- proof
  apply StatMech.Lattice.crossEdge_mk x y

/--
[isOpen_iff_dual_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma isOpen_iff_dual_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  ω e = true ↔ dualConfig ω (crossEdge e) = false := by
-- proof
  apply StatMech.Lattice.isOpen_iff_dual_isClosed ω e

/--
[dual_isOpen_iff_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma dual_isOpen_iff_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  dualConfig ω e = true ↔ ω (crossEdge.symm e) = false := by
-- proof
  apply StatMech.Lattice.dual_isOpen_iff_isClosed ω e

/--
[dualConfig_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean)
-/
@[path]
private lemma dualConfig_dualConfig_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  dualConfig (dualConfig ω) e = ω (crossEdge.symm (crossEdge.symm e)) := by
-- proof
  apply StatMech.Lattice.dualConfig_dualConfig ω e


-- created on 2026-10-23
