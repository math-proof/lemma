import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian
open StatMech StatMech.FrontierA StatMech.FrontierA.finiteCRSFCycleSupport


/--
[det_finiteTwistedLaplacian_permutation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_permutation_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian conductance transport).det = ∑ sigma : Equiv.Perm V, Equiv.Perm.sign sigma • ∏ v : V, if sigma v = v then ∑ u, conductance (sigma v) u else -conductance (sigma v) v * transport (sigma v) v := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_permutation conductance transport

/--
[finiteCRSFWitnessNext_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma finiteCRSFWitnessNext_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {X : finiteCRSFWitness V}
  {v : V}
-- given
  (hv : X.1 v = v) :
-- imply
  finiteCRSFWitnessNext X v = X.2 ⟨v, hv⟩ := by
-- proof
  apply StatMech.FrontierA.finiteCRSFWitnessNext_fixed X v hv

/--
[finiteCRSFWitnessNext_nonfixed_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma finiteCRSFWitnessNext_nonfixed_cycle_eq
  [Fintype V]
  [DecidableEq V]
  {X : finiteCRSFWitness V}
  {v : V}
-- given
  (hv : X.1 v ≠ v) :
-- imply
  finiteCRSFWitnessNext X (X.1 v) = v := by
-- proof
  apply StatMech.FrontierA.finiteCRSFWitnessNext_nonfixed_cycle X v hv

/--
[finiteCRSFWitnessNext_injectiveOn_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma finiteCRSFWitnessNext_injectiveOn_support_eq
  [Fintype V]
  [DecidableEq V]
  {X : finiteCRSFWitness V} :
-- imply
  Set.InjOn (finiteCRSFWitnessNext X) X.1.support := by
-- proof
  apply StatMech.FrontierA.finiteCRSFWitnessNext_injectiveOn_support X

/--
[det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitness_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian conductance transport).det = ∑ X : finiteCRSFWitness V, finiteCRSFWitnessTerm conductance transport X := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitness conductance transport

/--
[finiteCRSFAtomicCycle_support_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma finiteCRSFAtomicCycle_support_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {cycle cycle' : finiteCRSFAtomicCycle next}
-- given
  (hne : cycle ≠ cycle') :
-- imply
  Disjoint cycle.1.support cycle'.1.support := by
-- proof
  apply StatMech.FrontierA.finiteCRSFAtomicCycle_support_disjoint hne

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma ext_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S T : finiteCRSFCycleSupport next}
-- given
  (hcarrier : S.carrier = T.carrier) :
-- imply
  S = T := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.ext hcarrier

/--
[ambientPerm_apply_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma ambientPerm_apply_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
  {v : V}
-- given
  (hv : v ∈ S.carrier) :
-- imply
  S.ambientPerm v = S.restrictedPerm.symm ⟨v, hv⟩ := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.ambientPerm_apply_of_mem S hv

/--
[ambientPerm_apply_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma ambientPerm_apply_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
  {v : V}
-- given
  (hv : v ∉ S.carrier) :
-- imply
  S.ambientPerm v = v := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.ambientPerm_apply_of_not_mem S hv

/--
[ambientPerm_symm_apply_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma ambientPerm_symm_apply_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
  {v : V}
-- given
  (hv : v ∈ S.carrier) :
-- imply
  S.ambientPerm.symm v = next v := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.ambientPerm_symm_apply_of_mem S hv

/--
[ambientPerm_ne_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma ambientPerm_ne_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
  {v : V}
-- given
  (hv : v ∈ S.carrier) :
-- imply
  S.ambientPerm v ≠ v := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.ambientPerm_ne_of_mem S hv

/--
[ambientPerm_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma ambientPerm_support_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  S.ambientPerm.support = S.carrier := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.ambientPerm_support S

/--
[next_toWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma next_toWitness_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  finiteCRSFWitnessNext S.toWitness = next := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.next_toWitness S

/--
[restrictedPerm_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma restrictedPerm_support_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  S.restrictedPerm.support = Finset.univ := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.restrictedPerm_support S

/--
[mem_atomicCycles_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma mem_atomicCycles_isCycle_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
  {cycle : Equiv.Perm (↑S.carrier)}
-- given
  (hcycle : cycle ∈ S.atomicCycles) :
-- imply
  cycle.IsCycle := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.mem_atomicCycles_isCycle S hcycle

/--
[exists_mem_atomicCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma exists_mem_atomicCycle_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
  {v : ↑S.carrier} :
-- imply
  ∃ cycle ∈ S.atomicCycles, v ∈ cycle.support := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.exists_mem_atomicCycle S v

/--
[atomicCycle_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma atomicCycle_apply_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
  {cycle : Equiv.Perm (↑S.carrier)}
  {v : ↑S.carrier}
-- given
  (hcycle : cycle ∈ S.atomicCycles)
  (hv : v ∈ cycle.support) :
-- imply
  (cycle v : V) = next v := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.atomicCycle_apply S hcycle v hv

/--
[mem_toAtomicCycles_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma mem_toAtomicCycles_support_subset_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
  {cycle : finiteCRSFAtomicCycle next}
-- given
  (hcycle : cycle ∈ S.toAtomicCycles) :
-- imply
  cycle.1.support ⊆ S.carrier := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.mem_toAtomicCycles_support_subset S hcycle

/--
[mem_toAtomicCycles_iff_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma mem_toAtomicCycles_iff_support_subset_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
  {cycle : finiteCRSFAtomicCycle next} :
-- imply
  cycle ∈ S.toAtomicCycles ↔ cycle.1.support ⊆ S.carrier := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.mem_toAtomicCycles_iff_support_subset S cycle

/--
[carrier_ofAtomicCycles_toAtomicCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma carrier_ofAtomicCycles_toAtomicCycles_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  (ofAtomicCycles S.toAtomicCycles).carrier = S.carrier := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.carrier_ofAtomicCycles_toAtomicCycles S

/--
[ofAtomicCycles_toAtomicCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma ofAtomicCycles_toAtomicCycles_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  ofAtomicCycles S.toAtomicCycles = S := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.ofAtomicCycles_toAtomicCycles S

/--
[toAtomicCycles_ofAtomicCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma toAtomicCycles_ofAtomicCycles_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {selected : Finset (finiteCRSFAtomicCycle next)} :
-- imply
  (ofAtomicCycles selected).toAtomicCycles = selected := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.toAtomicCycles_ofAtomicCycles selected

/--
[support_toAtomicCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma support_toAtomicCycle_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (cycle : {cycle // cycle ∈ S.atomicCycles}) :
-- imply
  (S.toAtomicCycle cycle).1.support = cycle.1.support.map (Function.Embedding.subtype fun v => v ∈ S.carrier) := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.support_toAtomicCycle S cycle

/--
[holonomy_toAtomicCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma holonomy_toAtomicCycle_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (transport : V -> V -> Complex)
  (cycle : {cycle // cycle ∈ S.atomicCycles}) :
-- imply
  (S.toAtomicCycle cycle).holonomy transport = S.atomicCycleHolonomy transport cycle.1 := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.holonomy_toAtomicCycle transport S cycle

/--
[card_toAtomicCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma card_toAtomicCycles_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  S.toAtomicCycles.card = S.atomicCycles.card := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.card_toAtomicCycles S

/--
[prod_holonomy_toAtomicCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma prod_holonomy_toAtomicCycles_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (transport : V -> V -> Complex) :
-- imply
  (∏ cycle ∈ S.toAtomicCycles, cycle.holonomy transport) = ∏ cycle ∈ S.atomicCycles, S.atomicCycleHolonomy transport cycle := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.prod_holonomy_toAtomicCycles transport S

/--
[prod_transport_eq_prod_atomicCycleHolonomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma prod_transport_eq_prod_atomicCycleHolonomy_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (transport : V -> V -> Complex) :
-- imply
  (∏ v ∈ S.carrier, transport v (next v)) = ∏ cycle ∈ S.atomicCycles, S.atomicCycleHolonomy transport cycle := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.prod_transport_eq_prod_atomicCycleHolonomy transport S

/--
[sign_ambientPerm_eq_atomicCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma sign_ambientPerm_eq_atomicCycles_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  Equiv.Perm.sign S.ambientPerm = (-1 : ℤˣ) ^ (S.carrier.card + S.atomicCycles.card) := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.sign_ambientPerm_eq_atomicCycles S

/--
[finiteCRSFCycleSupport.toFiber_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma toFiber_support_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  S.toFiber.1.1.support = S.carrier := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.toFiber_support S

/--
[finiteCRSFCycleSupport.toCycleSupport_toFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma toCycleSupport_toFiber_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  S.toFiber.toCycleSupport = S := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.toCycleSupport_toFiber S

/--
[finiteCRSFWitnessFiber_support_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma finiteCRSFWitnessFiber_support_injective_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (next : V -> V) :
-- imply
  Function.Injective (fun X : finiteCRSFWitnessFiber next => X.1.1.support) := by
-- proof
  apply StatMech.FrontierA.finiteCRSFWitnessFiber_support_injective next

/--
[finiteCRSFWitnessFiber.toFiber_toCycleSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma toFiber_toCycleSupport_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {X : finiteCRSFWitnessFiber next} :
-- imply
  X.toCycleSupport.toFiber = X := by
-- proof
  apply StatMech.FrontierA.finiteCRSFWitnessFiber.toFiber_toCycleSupport X

/--
[finiteCRSFWitnessTerm_toFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma finiteCRSFWitnessTerm_toFiber_eq
  [Fintype V]
  [DecidableEq V]
  {S : finiteCRSFCycleSupport next}
-- given
  (conductance transport : V -> V -> Complex)
  (next : V -> V) :
-- imply
  finiteCRSFWitnessTerm conductance transport S.toFiber = S.term conductance transport := by
-- proof
  apply StatMech.FrontierA.finiteCRSFWitnessTerm_toFiber conductance transport next S

/--
[finiteCRSFCycleSupport.term_eq_atomicCycleSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma term_eq_atomicCycleSign_eq
  [Fintype V]
  [DecidableEq V]
  {S : finiteCRSFCycleSupport next}
-- given
  (conductance transport : V -> V -> Complex)
  (next : V -> V) :
-- imply
  S.term conductance transport = (-1 : Complex) ^ S.atomicCycles.card * ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier), conductance v (next v)) * ∏ v ∈ S.carrier, conductance v (next v) * transport v (next v)) := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.term_eq_atomicCycleSign conductance transport next S

/--
[finiteCRSFCycleSupport.term_eq_atomicCycleHolonomies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma term_eq_atomicCycleHolonomies_eq
  [Fintype V]
  [DecidableEq V]
  {S : finiteCRSFCycleSupport next}
-- given
  (conductance transport : V -> V -> Complex)
  (next : V -> V) :
-- imply
  S.term conductance transport = (-1 : Complex) ^ S.atomicCycles.card * ((∏ v : V, conductance v (next v)) * ∏ cycle ∈ S.atomicCycles, S.atomicCycleHolonomy transport cycle) := by
-- proof
  apply StatMech.FrontierA.finiteCRSFCycleSupport.term_eq_atomicCycleHolonomies conductance transport next S

/--
[det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitnessFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitnessFiber_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian conductance transport).det = ∑ next : V -> V, ∑ X : finiteCRSFWitnessFiber next, finiteCRSFWitnessTerm conductance transport X := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitnessFiber conductance transport

/--
[det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupport_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian conductance transport).det = ∑ next : V -> V, ∑ S : finiteCRSFCycleSupport next, finiteCRSFWitnessTerm conductance transport S.toFiber := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupport conductance transport

/--
[det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupportTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupportTerm_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian conductance transport).det = ∑ next : V -> V, ∑ S : finiteCRSFCycleSupport next, S.term conductance transport := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupportTerm conductance transport

/--
[det_finiteTwistedLaplacian_eq_sum_atomicCycleHolonomies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_eq_sum_atomicCycleHolonomies_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian conductance transport).det = ∑ next : V -> V, (∏ v : V, conductance v (next v)) * ∑ S : finiteCRSFCycleSupport next, (-1 : Complex) ^ S.atomicCycles.card * ∏ cycle ∈ S.atomicCycles, S.atomicCycleHolonomy transport cycle := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_eq_sum_atomicCycleHolonomies conductance transport

/--
[finiteTwistedLaplacian_trivial_mulVec_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma finiteTwistedLaplacian_trivial_mulVec_one_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance : V -> V -> Complex)
  (hdiag : forall v, conductance v v = 0) :
-- imply
  finiteTwistedLaplacian conductance (fun _ _ => 1) *ᵥ (fun _ => (1 : Complex)) = 0 := by
-- proof
  apply StatMech.FrontierA.finiteTwistedLaplacian_trivial_mulVec_one conductance hdiag

/--
[det_finiteTwistedLaplacian_trivial_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_trivial_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
-- given
  (conductance : V -> V -> Complex)
  (hdiag : forall v, conductance v v = 0) :
-- imply
  (finiteTwistedLaplacian conductance (fun _ _ => 1)).det = 0 := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_trivial_eq_zero conductance hdiag

/--
[finiteTwistedLaplacian_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma finiteTwistedLaplacian_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {a : Complex}
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  finiteTwistedLaplacian (fun v w => a * conductance v w) transport = a • finiteTwistedLaplacian conductance transport := by
-- proof
  apply StatMech.FrontierA.finiteTwistedLaplacian_const_mul a conductance transport

/--
[det_finiteTwistedLaplacian_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {a : Complex}
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian (fun v w => a * conductance v w) transport).det = a ^ Fintype.card V * (finiteTwistedLaplacian conductance transport).det := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_const_mul a conductance transport

/--
[isoradialMuConductance_eq_I_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma isoradialMuConductance_eq_I_mul_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (theta : V -> V -> Real) :
-- imply
  isoradialMuConductance theta = fun v w => Complex.I * isoradialLaplacianConductance theta v w := by
-- proof
  apply StatMech.FrontierA.isoradialMuConductance_eq_I_mul theta

/--
[finiteTwistedLaplacian_isoradialMu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma finiteTwistedLaplacian_isoradialMu_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (theta : V -> V -> Real)
  (transport : V -> V -> Complex) :
-- imply
  finiteTwistedLaplacian (isoradialMuConductance theta) transport = Complex.I • finiteTwistedLaplacian (isoradialLaplacianConductance theta) transport := by
-- proof
  apply StatMech.FrontierA.finiteTwistedLaplacian_isoradialMu theta transport

/--
[det_finiteTwistedLaplacian_isoradialMu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_isoradialMu_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (theta : V -> V -> Real)
  (transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian (isoradialMuConductance theta) transport).det = Complex.I ^ Fintype.card V * (finiteTwistedLaplacian (isoradialLaplacianConductance theta) transport).det := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_isoradialMu theta transport

/--
[neg_one_mul_coneQuarterPhase_mul_I](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma neg_one_mul_coneQuarterPhase_mul_I_eq
  [Fintype V]
  [DecidableEq V]
  {v : V}
-- given
  (exceptional : V -> Bool) :
-- imply
  (-1 : Complex) * coneQuarterPhase exceptional v * Complex.I = if exceptional v then -1 else 1 := by
-- proof
  apply StatMech.FrontierA.neg_one_mul_coneQuarterPhase_mul_I exceptional v

/--
[conePhase_prefactor_eq_exceptionSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma conePhase_prefactor_eq_exceptionSign_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (exceptional : V -> Bool) :
-- imply
  (-1 : Complex) ^ Fintype.card V * (∏ v : V, coneQuarterPhase exceptional v) * Complex.I ^ Fintype.card V = (-1 : Complex) ^ coneExceptionCount exceptional := by
-- proof
  apply StatMech.FrontierA.conePhase_prefactor_eq_exceptionSign exceptional

/--
[sum_cycleSelections_eq_prod_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma sum_cycleSelections_eq_prod_one_sub_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype C]
-- given
  (holonomy : C -> Complex) :
-- imply
  (∑ selected : Finset C, (-1 : Complex) ^ selected.card * ∏ c ∈ selected, holonomy c) = ∏ c : C, (1 - holonomy c) := by
-- proof
  apply StatMech.FrontierA.sum_cycleSelections_eq_prod_one_sub holonomy

/--
[pairedBoundaryCharacter_eq_formanCycleCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma pairedBoundaryCharacter_eq_formanCycleCoefficient_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (holonomy : Complex)
  (hholonomy : holonomy ≠ 0) :
-- imply
  (1 - holonomy) * (1 - holonomy⁻¹) = formanCycleCoefficient holonomy := by
-- proof
  apply StatMech.FrontierA.pairedBoundaryCharacter_eq_formanCycleCoefficient holonomy hholonomy

/--
[prod_pairedBoundaryCharacter_eq_formanCRSFCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma prod_pairedBoundaryCharacter_eq_formanCRSFCoefficient_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype C]
-- given
  (holonomy : C -> Complex)
  (hholonomy : forall c, holonomy c ≠ 0) :
-- imply
  (∏ c : C, (1 - holonomy c) * (1 - (holonomy c)⁻¹)) = formanCRSFCoefficient holonomy := by
-- proof
  apply StatMech.FrontierA.prod_pairedBoundaryCharacter_eq_formanCRSFCoefficient holonomy hholonomy

/--
[criticalKacWard_det_eq_laplacian_of_subgraphFactorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean)
-/
@[path]
private lemma criticalKacWard_det_eq_laplacian_of_subgraphFactorization_eq
  [Fintype V]
  [DecidableEq V]
  {kacWard : Matrix D D Complex}
-- given
  (thetaVertex : V -> V -> Real)
  (thetaEdge : E -> Real)
  (transport : V -> V -> Complex)
  (exceptional : V -> Bool)
  (hsubgraphFactorization : (1 - kacWard).det = (((-1 : Complex) ^ Fintype.card V * kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) * (∏ v : V, coneQuarterPhase exceptional v) * kwLaplacianEdgePrefactor thetaEdge) * (finiteTwistedLaplacian (isoradialMuConductance thetaVertex) transport).det)) :
-- imply
  (1 - kacWard).det = (-1 : Complex) ^ coneExceptionCount exceptional * kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) * kwLaplacianEdgePrefactor thetaEdge * (finiteTwistedLaplacian (isoradialLaplacianConductance thetaVertex) transport).det := by
-- proof
  apply StatMech.FrontierA.criticalKacWard_det_eq_laplacian_of_subgraphFactorization kacWard thetaVertex thetaEdge transport exceptional hsubgraphFactorization


-- created on 2026-10-23
