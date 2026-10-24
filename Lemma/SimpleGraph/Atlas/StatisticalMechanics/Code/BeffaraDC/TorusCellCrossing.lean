import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing
open SimpleGraph StatMech StatMech.BeffaraDC


/--
[torusHorizontalEdge_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusHorizontalEdge_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusHorizontalEdge L x y : Sym2 (ZMod L × ZMod L)) = s((x, y), (x + 1, y)) := by
-- proof
  apply StatMech.BeffaraDC.torusHorizontalEdge_val L x y

/--
[torusVerticalEdge_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusVerticalEdge_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusVerticalEdge L x y : Sym2 (ZMod L × ZMod L)) = s((x, y), (x, y + 1)) := by
-- proof
  apply StatMech.BeffaraDC.torusVerticalEdge_val L x y

/--
[torusHorizontalEdge_orientation_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusHorizontalEdge_orientation_independent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusHorizontalEdge L x y : Sym2 (ZMod L × ZMod L)) = s((x + 1, y), (x, y)) := by
-- proof
  apply StatMech.BeffaraDC.torusHorizontalEdge_orientation_independent L x y

/--
[torusVerticalEdge_orientation_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusVerticalEdge_orientation_independent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusVerticalEdge L x y : Sym2 (ZMod L × ZMod L)) = s((x, y + 1), (x, y)) := by
-- proof
  apply StatMech.BeffaraDC.torusVerticalEdge_orientation_independent L x y

/--
[torusEdgeOfCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusEdgeOfCode_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (torusEdgeOfCode L) := by
-- proof
  apply StatMech.BeffaraDC.torusEdgeOfCode_injective L

/--
[torusEdgeOfCode_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusEdgeOfCode_surjective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Surjective (torusEdgeOfCode L) := by
-- proof
  apply StatMech.BeffaraDC.torusEdgeOfCode_surjective L

/--
[torusEdgeCodeEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusEdgeCodeEquiv_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {c : TorusEdgeCode L} :
-- imply
  torusEdgeCodeEquiv L c = torusEdgeOfCode L c := by
-- proof
  apply StatMech.BeffaraDC.torusEdgeCodeEquiv_apply L c

/--
[torusCellCrossing_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_horizontal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  torusCellCrossing L (torusHorizontalEdge L x y) = torusVerticalEdge L x (y - 1) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_horizontal L x y

/--
[torusCellCrossing_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_vertical_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  torusCellCrossing L (torusVerticalEdge L x y) = torusHorizontalEdge L (x - 1) y := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_vertical L x y

/--
[torusCellCrossing_horizontal_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_horizontal_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusCellCrossing L (torusHorizontalEdge L x y) : Sym2 (ZMod L × ZMod L)) = s((x, y - 1), (x, y)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_horizontal_val L x y

/--
[torusCellCrossing_vertical_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_vertical_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusCellCrossing L (torusVerticalEdge L x y) : Sym2 (ZMod L × ZMod L)) = s((x - 1, y), (x, y)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_vertical_val L x y

/--
[torusCellCrossing_of_reversed_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_of_reversed_horizontal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : TorusAmbientEdge L}
  {x y : ZMod L}
-- given
  (he : (e : Sym2 (ZMod L × ZMod L)) = s((x + 1, y), (x, y))) :
-- imply
  torusCellCrossing L e = torusVerticalEdge L x (y - 1) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_of_reversed_horizontal L e x y he

/--
[torusCellCrossing_of_reversed_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_of_reversed_vertical_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : TorusAmbientEdge L}
  {x y : ZMod L}
-- given
  (he : (e : Sym2 (ZMod L × ZMod L)) = s((x, y + 1), (x, y))) :
-- imply
  torusCellCrossing L e = torusHorizontalEdge L (x - 1) y := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_of_reversed_vertical L e x y he

/--
[torusCellCrossing_symm_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_symm_horizontal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusCellCrossing L).symm (torusHorizontalEdge L x y) = torusVerticalEdge L (x + 1) y := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_symm_horizontal L x y

/--
[torusCellCrossing_symm_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_symm_vertical_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusCellCrossing L).symm (torusVerticalEdge L x y) = torusHorizontalEdge L x (y + 1) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_symm_vertical L x y

/--
[torusCellCrossing_mem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_mem_edgeFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : TorusAmbientEdge L} :
-- imply
  (torusCellCrossing L e : Sym2 (ZMod L × ZMod L)) ∈ (onsTorusGraph L).edgeFinset := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_mem_edgeFinset L e

/--
[torusCellCrossing_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (torusCellCrossing L) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_injective L

/--
[torusCellCrossing_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_surjective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Surjective (torusCellCrossing L) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_surjective L

/--
[torusCellCrossing_symm_apply_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_symm_apply_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : TorusAmbientEdge L} :
-- imply
  (torusCellCrossing L).symm (torusCellCrossing L e) = e := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_symm_apply_apply L e

/--
[torusCellCrossing_apply_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean)
-/
@[path]
private lemma torusCellCrossing_apply_symm_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : TorusAmbientEdge L} :
-- imply
  torusCellCrossing L ((torusCellCrossing L).symm e) = e := by
-- proof
  apply StatMech.BeffaraDC.torusCellCrossing_apply_symm_apply L e


-- created on 2026-10-23
