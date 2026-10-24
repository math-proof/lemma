import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.InterfaceConnected
open SimpleGraph Function StatMech StatMech.Lattice


/--
[dartNext_head_eq_iff_front_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma dartNext_head_eq_iff_front_mem_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  (dartNext K e).head = e.head ↔ e.head + (-rot90Fun e.dir) ∈ K := by
-- proof
  apply StatMech.Lattice.dartNext_head_eq_iff_front_mem K e

/--
[dartNext_rotates_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma dartNext_rotates_head_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hA : e.head + (-rot90Fun e.dir) ∈ K) :
-- imply
  (dartNext K e).head = e.head ∧ (dartNext K e).dir = rot90Fun e.dir := by
-- proof
  apply StatMech.Lattice.dartNext_rotates_head K e hA

/--
[dart_eq_of_common_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma dart_eq_of_common_head_eq
  {e f : Dart}
-- given
  (hh : e.head = f.head)
  (hd : e.dir = f.dir) :
-- imply
  e = f := by
-- proof
  apply StatMech.Lattice.dart_eq_of_common_head hh hd

/--
[dartNext_dir_eq_rot90_of_front](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma dartNext_dir_eq_rot90_of_front_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hA : e.head + (-rot90Fun e.dir) ∈ K) :
-- imply
  (dartNext K e).dir = rot90Fun e.dir := by
-- proof
  apply StatMech.Lattice.dartNext_dir_eq_rot90_of_front K e hA

/--
[dartNext_iterate_head_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma dartNext_iterate_head_fixed_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  ∀ (k : ℕ), (∀ j < k, IsInnerCorner K ((dartNext K)^[j] e)) → ((dartNext K)^[k] e).head = e.head ∧ ((dartNext K)^[k] e).dir = (rot90Fun)^[k] e.dir := by
-- proof
  apply StatMech.Lattice.dartNext_iterate_head_fixed K e

/--
[dartNext_iterate_isBoundary_head_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma dartNext_iterate_isBoundary_head_fixed_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart K e)
  (hcorner : ∀ j < k, IsInnerCorner K ((dartNext K)^[j] e)) :
-- imply
  IsBoundaryDart K ((dartNext K)^[k] e) ∧ ((dartNext K)^[k] e).head = e.head ∧ ((dartNext K)^[k] e).dir = (rot90Fun)^[k] e.dir := by
-- proof
  apply StatMech.Lattice.dartNext_iterate_isBoundary_head_fixed K e he k hcorner

/--
[SameOrbit.refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma refl_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  SameOrbit K e e := by
-- proof
  apply StatMech.Lattice.SameOrbit.refl K e

/--
[SameOrbit.trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma trans_eq
  {K : Set (Site 2)}
  {e f g : Dart}
-- given
  (h0 : SameOrbit K e f)
  (h1 : SameOrbit K f g) :
-- imply
  SameOrbit K e g := by
-- proof
  apply StatMech.Lattice.SameOrbit.trans h0 h1

/--
[SameOrbit.symm_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma symm_of_finite_eq
  {K : Set (Site 2)}
  {e f : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (h : SameOrbit K e f) :
-- imply
  SameOrbit K f e := by
-- proof
  apply StatMech.Lattice.SameOrbit.symm_of_finite hK he h

/--
[sameComponent_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma sameComponent_of_sameOrbit_eq
  {K : Set (Site 2)}
  {e f : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hf : IsBoundaryDart K f)
  (h : SameOrbit K e f) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
-- proof
  apply StatMech.Lattice.sameComponent_of_sameOrbit K he hf h

/--
[interfaceConnected_iff_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma interfaceConnected_iff_sameOrbit_eq
  {K : Set (Site 2)} :
-- imply
  InterfaceConnected K ↔ ∀ (e f : Dart) (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f), ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ → SameOrbit K e f := by
-- proof
  apply StatMech.Lattice.interfaceConnected_iff_sameOrbit K

/--
[interfaceConnected_of_orbitHeadsSaturate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma interfaceConnected_of_orbitHeadsSaturate_eq
  {K : Set (Site 2)}
-- given
  (h : OrbitHeadsSaturate K) :
-- imply
  InterfaceConnected K := by
-- proof
  apply StatMech.Lattice.interfaceConnected_of_orbitHeadsSaturate K h

/--
[orbitHeadsSaturate_of_interfaceConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma orbitHeadsSaturate_of_interfaceConnected_eq
  {K : Set (Site 2)}
-- given
  (h : InterfaceConnected K) :
-- imply
  OrbitHeadsSaturate K := by
-- proof
  apply StatMech.Lattice.orbitHeadsSaturate_of_interfaceConnected K h

/--
[KingAdj.symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma symm_eq
  {u v : Site 2}
-- given
  (h : KingAdj u v) :
-- imply
  KingAdj v u := by
-- proof
  apply StatMech.Lattice.KingAdj.symm h

/--
[boundaryKingGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma boundaryKingGraph_adj_eq
  {K : Set (Site 2)}
  {a b : ↥(Kᶜ : Set (Site 2))} :
-- imply
  (boundaryKingGraph K).Adj a b ↔ KingAdj (a : Site 2) (b : Site 2) := by
-- proof
  apply StatMech.Lattice.boundaryKingGraph_adj K a b

/--
[orbitReached_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma orbitReached_self_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  OrbitReached K e e.head := by
-- proof
  apply StatMech.Lattice.orbitReached_self K e he

/--
[orbitReached_of_kingReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma orbitReached_of_kingReachable_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u w : Site 2}
-- given
  (htr : OrbitKingTransport K)
  (he : IsBoundaryDart K e)
  (hu : u ∉ K)
  (hw : w ∉ K)
  (hreach : (boundaryKingGraph K).Reachable ⟨u, hu⟩ ⟨w, hw⟩)
  (hou : OrbitReached K e u) :
-- imply
  OrbitReached K e w := by
-- proof
  apply StatMech.Lattice.orbitReached_of_kingReachable K htr e he hu hw hreach hou

/--
[interfaceConnected_of_kingResidues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean)
-/
@[path]
private lemma interfaceConnected_of_kingResidues_eq
  {K : Set (Site 2)}
-- given
  (htr : OrbitKingTransport K)
  (hcon : BoundaryKingConnected K)
  (hsat : OrbitVertexSaturate K) :
-- imply
  InterfaceConnected K := by
-- proof
  apply StatMech.Lattice.interfaceConnected_of_kingResidues K htr hcon hsat


-- created on 2026-10-23
