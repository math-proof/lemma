import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponent.Part2
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[grahamComponentComplement_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean)
-/
@[path]
private lemma grahamComponentComplement_not_mem_eq
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u : W} :
-- imply
  u ∉ grahamComponentComplement ends m u := by
-- proof
  apply StatMech.FrontierA.grahamComponentComplement_not_mem ends m u

/--
[grahamComponentComplement_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean)
-/
@[path]
private lemma grahamComponentComplement_noCrossing_eq
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u : W} :
-- imply
  NoCrossingK ends m (grahamComponentComplement ends m u) := by
-- proof
  apply StatMech.FrontierA.grahamComponentComplement_noCrossing ends m u

/--
[grahamComponentComplement_noCrossing_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean)
-/
@[path]
private lemma grahamComponentComplement_noCrossing_of_subset_eq
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 W}
  {m K : Finset ι}
  {u : W}
-- given
  (hKm : K ⊆ m) :
-- imply
  NoCrossingK ends K (grahamComponentComplement ends m u) := by
-- proof
  apply StatMech.FrontierA.grahamComponentComplement_noCrossing_of_subset ends m K u hKm

/--
[edgeInsideK_componentComplement_of_mem_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean)
-/
@[path]
private lemma edgeInsideK_componentComplement_of_mem_sdiff_eq
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u : W}
  {i : ι}
-- given
  (hi : i ∈ m \ grahamSuperpositionBondComponent ends m u) :
-- imply
  edgeInsideK ends (grahamComponentComplement ends m u) i := by
-- proof
  apply StatMech.FrontierA.edgeInsideK_componentComplement_of_mem_sdiff ends m u hi

/--
[mem_sdiff_component_of_edgeInsideK_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean)
-/
@[path]
private lemma mem_sdiff_component_of_edgeInsideK_complement_eq
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u : W}
  {i : ι}
-- given
  (him : i ∈ m)
  (hi : edgeInsideK ends (grahamComponentComplement ends m u) i) :
-- imply
  i ∈ m \ grahamSuperpositionBondComponent ends m u := by
-- proof
  apply StatMech.FrontierA.mem_sdiff_component_of_edgeInsideK_complement ends m u him hi

/--
[mem_sdiff_component_iff_edgeInsideK_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean)
-/
@[path]
private lemma mem_sdiff_component_iff_edgeInsideK_complement_eq
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u : W}
  {i : ι} :
-- imply
  i ∈ m \ grahamSuperpositionBondComponent ends m u ↔ i ∈ m ∧ edgeInsideK ends (grahamComponentComplement ends m u) i := by
-- proof
  apply StatMech.FrontierA.mem_sdiff_component_iff_edgeInsideK_complement ends m u

/--
[couplingIn_componentComplement_endsM](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean)
-/
@[path]
private lemma couplingIn_componentComplement_endsM_eq
  [DecidableEq ι]
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {u : V}
  {i : Copy G m}
-- given
  (hi : i ∈ (Finset.univ : Finset (Copy G m)) \ grahamSuperpositionBondComponent (endsM G m) Finset.univ u) :
-- imply
  StatMech.Sharpness.couplingIn J (grahamComponentComplement (endsM G m) Finset.univ u) (endsM G m i) = J (endsM G m i) := by
-- proof
  apply StatMech.FrontierA.couplingIn_componentComplement_endsM G J m u hi

/--
[couplingIn_componentComplement_eq_zero_of_mem_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean)
-/
@[path]
private lemma couplingIn_componentComplement_eq_zero_of_mem_component_eq
  [DecidableEq ι]
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {u : V}
  {i : Copy G m}
-- given
  (hi : i ∈ grahamSuperpositionBondComponent (endsM G m) Finset.univ u) :
-- imply
  StatMech.Sharpness.couplingIn J (grahamComponentComplement (endsM G m) Finset.univ u) (endsM G m i) = 0 := by
-- proof
  apply StatMech.FrontierA.couplingIn_componentComplement_eq_zero_of_mem_component G J m u hi


-- created on 2026-10-23
