import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectWalkWinding_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectWalkWinding_append_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y z : R.Vertex}
  {p : G.Walk x y}
  {q : G.Walk y z} :
-- imply
  fkRectWalkWinding R (p.append q) = ((fkRectWalkWinding R p).1 + (fkRectWalkWinding R q).1, (fkRectWalkWinding R p).2 + (fkRectWalkWinding R q).2) := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_append R p q

/--
[fkRectHorizontalSeamIncrement_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectHorizontalSeamIncrement_swap_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  fkRectHorizontalSeamIncrement R y x = -fkRectHorizontalSeamIncrement R x y := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalSeamIncrement_swap R x y

/--
[fkRectVerticalSeamIncrement_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectVerticalSeamIncrement_swap_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  fkRectVerticalSeamIncrement R y x = -fkRectVerticalSeamIncrement R x y := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamIncrement_swap R x y

/--
[fkRectWalkWinding_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectWalkWinding_reverse_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {p : G.Walk x y} :
-- imply
  fkRectWalkWinding R p.reverse = (-(fkRectWalkWinding R p).1, -(fkRectWalkWinding R p).2) := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_reverse R p

/--
[fkRectWalkWinding_conjugate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectWalkWinding_conjugate_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {r : G.Walk x y}
  {p : G.Walk y y} :
-- imply
  fkRectWalkWinding R ((r.append p).append r.reverse) = fkRectWalkWinding R p := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_conjugate R r p

/--
[FKRectHasNet.of_connected_closedWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma of_connected_closedWalks_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x x}
  {q : (fkRectOpenGraph R omega).Walk y y}
-- given
  (hxy : (fkRectOpenGraph R omega).Reachable x y)
  (hind : FKRectWindingIndependent (fkRectWalkWinding R p) (fkRectWalkWinding R q)) :
-- imply
  FKRectHasNet R omega := by
-- proof
  apply StatMech.FrontierD.FKRectHasNet.of_connected_closedWalks R omega hxy p q hind

/--
[fkRectWalkWinding_mapLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectWalkWinding_mapLe_eq
  {R : FKRectTorus}
  {G H : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {p : G.Walk x y}
-- given
  (hGH : G ≤ H) :
-- imply
  fkRectWalkWinding R (p.mapLe hGH) = fkRectWalkWinding R p := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_mapLe R hGH p

/--
[fkRectOpenGraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectOpenGraph_mono_eq
  {R : FKRectTorus}
  {omega tau : R.Configuration}
-- given
  (hopen : ∀ e, omega e = true → tau e = true) :
-- imply
  fkRectOpenGraph R omega ≤ fkRectOpenGraph R tau := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_mono R hopen

/--
[FKRectHasNet.mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma mono_eq
  {R : FKRectTorus}
  {omega tau : R.Configuration}
-- given
  (hopen : ∀ e, omega e = true → tau e = true)
  (hnet : FKRectHasNet R omega) :
-- imply
  FKRectHasNet R tau := by
-- proof
  apply StatMech.FrontierD.FKRectHasNet.mono R hopen hnet

/--
[fkRectNetIndicator_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectNetIndicator_mono_eq
  {R : FKRectTorus}
  {omega tau : R.Configuration}
-- given
  (hopen : ∀ e, omega e = true → tau e = true) :
-- imply
  fkRectNetIndicator R omega ≤ fkRectNetIndicator R tau := by
-- proof
  apply StatMech.FrontierD.fkRectNetIndicator_mono R hopen

/--
[FKRectHasNet.mono_configurationOfEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma mono_configurationOfEdges_eq
  {R : FKRectTorus}
  {F A : Finset R.EdgeIndex}
-- given
  (hFA : F ⊆ A)
  (hnet : FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
-- imply
  FKRectHasNet R (fkRectConfigurationOfEdges R A) := by
-- proof
  apply StatMech.FrontierD.FKRectHasNet.mono_configurationOfEdges R hFA hnet

/--
[FKRectHasNet.insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma insert_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (hnet : FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
-- imply
  FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) := by
-- proof
  apply StatMech.FrontierD.FKRectHasNet.insert R F e hnet

/--
[fkRectWalkWinding_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectWalkWinding_empty_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R (fkRectConfigurationOfEdges R ∅)).Walk x y} :
-- imply
  fkRectWalkWinding R p = (0, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_empty R p

/--
[not_FKRectHasNet_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma not_FKRectHasNet_empty_eq
  {R : FKRectTorus} :
-- imply
  ¬ FKRectHasNet R (fkRectConfigurationOfEdges R ∅) := by
-- proof
  apply StatMech.FrontierD.not_FKRectHasNet_empty R

/--
[fkRectNetIndicator_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetMonotonicity.lean)
-/
@[path]
private lemma fkRectNetIndicator_empty_eq
  {R : FKRectTorus} :
-- imply
  fkRectNetIndicator R (fkRectConfigurationOfEdges R ∅) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectNetIndicator_empty R


-- created on 2026-10-23
