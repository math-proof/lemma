import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
open Set SimpleGraph MeasureTheory StatMech StatMech.Lattice


/--
[tpc_overlapComp_singleton_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean)
-/
@[path]
private lemma tpc_overlapComp_singleton_of_closed_eq
  {m m' c d : ℤ}
  {xB : Site 2}
  {z : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hz : z ∈ overlapComp (fun _ => false) m m' c d xB hxB) :
-- imply
  z = xB := by
-- proof
  apply StatMech.Lattice.tpc_overlapComp_singleton_of_closed m m' c d xB hxB z hz

/--
[tpc_arcS_twoPathsCross_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean)
-/
@[path]
private lemma tpc_arcS_twoPathsCross_false_eq :
-- imply
  ¬ ArcS_TwoPathsCross (fun _ => false) 0 1 0 0 0 1 ![0, 1] (by simp [rect]) := by
-- proof
  apply StatMech.Lattice.tpc_arcS_twoPathsCross_false

/--
[tpc_arcWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean)
-/
@[path]
private lemma tpc_arcWalk_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {m m' c d : ℤ}
  {xB : Site 2}
  {yT : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hyT : yT ∈ rect m m' c d)
  (h : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩) :
-- imply
  ∃ (V : (hypercubicLattice 2).Walk xB yT), ∀ z ∈ V.support, z ∈ overlapComp ω m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.tpc_arcWalk_support hxB hyT h

/--
[tpc_meets_of_separating_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean)
-/
@[path]
private lemma tpc_meets_of_separating_set_eq
  {P S : Set (Site 2)}
  {x y : Site 2}
  {γ : (hypercubicLattice 2).Walk x y}
-- given
  (hxS : x ∈ S)
  (hyS : y ∉ S)
  (hbd : ∀ u v : Site 2, (hypercubicLattice 2).Adj u v → s(u, v) ∈ γ.edges → bdEdge S s(u, v) → u ∈ P ∨ v ∈ P) :
-- imply
  ∃ z ∈ γ.support, z ∈ P := by
-- proof
  apply StatMech.Lattice.tpc_meets_of_separating_set γ hxS hyS hbd

/--
[tpc_two_paths_cross_of_sep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean)
-/
@[path]
private lemma tpc_two_paths_cross_of_sep_eq
  {P : Set (Site 2)}
  {α β c d : ℤ}
  {x y : Site 2}
  {γ : (hypercubicLattice 2).Walk x y}
-- given
  (hsep : ArcSeparatingSet P α β c d)
  (hx : x ∈ rect α β c d)
  (hy : y ∈ rect α β c d)
  (hx0 : x 0 = α)
  (hy0 : y 0 = β)
  (hsupp : ∀ z ∈ γ.support, z ∈ rect α β c d) :
-- imply
  ∃ z ∈ γ.support, z ∈ P := by
-- proof
  apply StatMech.Lattice.tpc_two_paths_cross_of_sep hsep hx hy hx0 hy0 γ hsupp

/--
[tpc_arc_sides_of_sep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean)
-/
@[path]
private lemma tpc_arc_sides_of_sep_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
-- given
  (hsep : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d), ArcSeparatingSet (overlapComp ω m m' c d xB hxB) α β c d) :
-- imply
  StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
-- proof
  apply StatMech.Lattice.tpc_arc_sides_of_sep ω hsep

/--
[tpc_rsw_strip_glue_of_sep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean)
-/
@[path]
private lemma tpc_rsw_strip_glue_of_sep_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hsepL : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d), ArcSeparatingSet (overlapComp ω m m' c d xB hxB) a m' c d)
  (hsepR : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d), ArcSeparatingSet (overlapComp ω m m' c d xB hxB) m b c d) :
-- imply
  μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) * μ.real (horizontalCrossingEvent m b c d) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Lattice.tpc_rsw_strip_glue_of_sep μ hpa ham hmm' hm'b hsepL hsepR


-- created on 2026-10-23
