import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetReflection.Part2
open Finset StatMech StatMech.FrontierA


/--
[multibondConfigReindex_cubicalDualVertexZReflect_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean)
-/
@[path]
private lemma multibondConfigReindex_cubicalDualVertexZReflect_none_eq
  {a b c : Nat}
-- given
  (s : CubicalDualVertex a b c -> Bool) :
-- imply
  multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s none = s none := by
-- proof
  apply StatMech.FrontierA.multibondConfigReindex_cubicalDualVertexZReflect_none s

/--
[multibondConfigReindex_cubicalDualVertexZReflect_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean)
-/
@[path]
private lemma multibondConfigReindex_cubicalDualVertexZReflect_some_eq
  {a b c : Nat}
  {q : CubicalCell a b c}
-- given
  (s : CubicalDualVertex a b c -> Bool) :
-- imply
  multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s (some (cubicalCellZReflect q)) = s (some q) := by
-- proof
  apply StatMech.FrontierA.multibondConfigReindex_cubicalDualVertexZReflect_some s q

/--
[multibondConfigReindex_cubicalDualVertexZReflect_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean)
-/
@[path]
private lemma multibondConfigReindex_cubicalDualVertexZReflect_mk_eq
  {a b c : Nat}
  {x : Fin a}
  {y : Fin b}
  {z : Fin c}
-- given
  (s : CubicalDualVertex a b c -> Bool) :
-- imply
  multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s (some (⟨x, y, z.rev⟩ : CubicalCell a b c)) = s (some ⟨x, y, z⟩) := by
-- proof
  apply StatMech.FrontierA.multibondConfigReindex_cubicalDualVertexZReflect_mk s x y z

/--
[finBackward_rev_map_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean)
-/
@[path]
private lemma finBackward_rev_map_rev_eq
  {n : Nat}
  {k : Fin (n + 1)} :
-- imply
  (finBackward k.rev).map Fin.rev = finForward k := by
-- proof
  apply StatMech.FrontierA.finBackward_rev_map_rev k

/--
[finForward_rev_map_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean)
-/
@[path]
private lemma finForward_rev_map_rev_eq
  {n : Nat}
  {k : Fin (n + 1)} :
-- imply
  (finForward k.rev).map Fin.rev = finBackward k := by
-- proof
  apply StatMech.FrontierA.finForward_rev_map_rev k

/--
[multibondConfigReindex_cubicalDualVertexZReflect_optionMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean)
-/
@[path]
private lemma multibondConfigReindex_cubicalDualVertexZReflect_optionMap_eq
  {a b c : Nat}
  {x : Fin a}
  {y : Fin b}
  {o : Option (Fin c)}
-- given
  (s : CubicalDualVertex a b c -> Bool) :
-- imply
  multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s (o.map fun z => (⟨x, y, z⟩ : CubicalCell a b c)) = s (o.map fun z => (⟨x, y, z.rev⟩ : CubicalCell a b c)) := by
-- proof
  apply StatMech.FrontierA.multibondConfigReindex_cubicalDualVertexZReflect_optionMap s x y o

/--
[cubicalPlaquetteZReflectEquiv_map_xySheet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean)
-/
@[path]
private lemma cubicalPlaquetteZReflectEquiv_map_xySheet_eq
  {a b c : Nat}
  {k : Fin (c + 1)} :
-- imply
  (cubicalXYSheet (a := a) (b := b) k).map (cubicalPlaquetteZReflectEquiv a b c).toEmbedding = cubicalXYSheet (a := a) (b := b) k.rev := by
-- proof
  apply StatMech.FrontierA.cubicalPlaquetteZReflectEquiv_map_xySheet k

/--
[cubicalDualEnds_zReflect_agrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean)
-/
@[path]
private lemma cubicalDualEnds_zReflect_agrees_eq
  {a b c : Nat}
  {p : CubicalPlaquette a b c}
-- given
  (s : CubicalDualVertex a b c -> Bool) :
-- imply
  (multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s) (cubicalDualEnds ((cubicalPlaquetteZReflectEquiv a b c) p)).1 = (multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s) (cubicalDualEnds ((cubicalPlaquetteZReflectEquiv a b c) p)).2 <-> s (cubicalDualEnds p).1 = s (cubicalDualEnds p).2 := by
-- proof
  apply StatMech.FrontierA.cubicalDualEnds_zReflect_agrees p s

/--
[multibondDisorderFreeEnergy_cubicalXYSheet_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_cubicalXYSheet_rev_eq
  {a b c : Nat}
  {beta : Real}
  {k : Fin (c + 1)} :
-- imply
  multibondDisorderFreeEnergy (cubicalDualEnds (a := a) (b := b) (c := c)) (fun _ : CubicalPlaquette a b c => beta) (cubicalXYSheet k.rev) = multibondDisorderFreeEnergy cubicalDualEnds (fun _ : CubicalPlaquette a b c => beta) (cubicalXYSheet k) := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_cubicalXYSheet_rev beta k


-- created on 2026-10-23
