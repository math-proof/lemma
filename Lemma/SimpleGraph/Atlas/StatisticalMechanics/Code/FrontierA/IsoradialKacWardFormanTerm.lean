import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanTerm
open StatMech StatMech.FrontierA


/--
[finiteCRSF_atomicCycleSupports_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean)
-/
@[path]
private lemma finiteCRSF_atomicCycleSupports_biUnion_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next} :
-- imply
  S.atomicCycles.biUnion (fun cycle => cycle.support) = Finset.univ := by
-- proof
  apply StatMech.FrontierA.finiteCRSF_atomicCycleSupports_biUnion S

/--
[finiteCRSF_prod_transport_eq_prod_atomicCycleHolonomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean)
-/
@[path]
private lemma finiteCRSF_prod_transport_eq_prod_atomicCycleHolonomy_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (transport : V -> V -> Complex) :
-- imply
  (∏ v ∈ S.carrier, transport v (next v)) = ∏ cycle ∈ S.atomicCycles, finiteCRSFAtomicCycleHolonomy transport S cycle := by
-- proof
  apply StatMech.FrontierA.finiteCRSF_prod_transport_eq_prod_atomicCycleHolonomy transport S

/--
[finiteCRSFSupportTransport_eq_prod_atomicCycleCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean)
-/
@[path]
private lemma finiteCRSFSupportTransport_eq_prod_atomicCycleCoefficient_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (transport : V -> V -> Complex) :
-- imply
  finiteCRSFSupportTransport transport S = ∏ cycle ∈ S.atomicCycles, finiteCRSFAtomicCycleCoefficient transport S cycle := by
-- proof
  apply StatMech.FrontierA.finiteCRSFSupportTransport_eq_prod_atomicCycleCoefficient transport S

/--
[finiteCRSF_nonfixed_product_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean)
-/
@[path]
private lemma finiteCRSF_nonfixed_product_reindex_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (∏ v ∈ (Finset.univ.filter fun v => S.ambientPerm v ≠ v), -conductance (S.ambientPerm v) v * transport (S.ambientPerm v) v) = ∏ v ∈ S.carrier, -conductance v (next v) * transport v (next v) := by
-- proof
  apply StatMech.FrontierA.finiteCRSF_nonfixed_product_reindex conductance transport S

/--
[finiteCRSF_fixed_product_eq_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean)
-/
@[path]
private lemma finiteCRSF_fixed_product_eq_complement_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (conductance : V -> V -> Complex) :
-- imply
  (∏ v : laplacianPermutationFixedPoint S.ambientPerm, conductance v (next v)) = ∏ v : {v : V // v ∉ S.carrier}, conductance v (next v) := by
-- proof
  apply StatMech.FrontierA.finiteCRSF_fixed_product_eq_complement conductance S

/--
[finiteCRSFWitnessTerm_toFiber_eq_outgoing_mul_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean)
-/
@[path]
private lemma finiteCRSFWitnessTerm_toFiber_eq_outgoing_mul_transport_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  finiteCRSFWitnessTerm conductance transport S.toFiber = finiteCRSFOutgoingConductance conductance next * finiteCRSFSupportTransport transport S := by
-- proof
  apply StatMech.FrontierA.finiteCRSFWitnessTerm_toFiber_eq_outgoing_mul_transport conductance transport S

/--
[det_finiteTwistedLaplacian_eq_sum_outgoing_mul_cycleTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_eq_sum_outgoing_mul_cycleTransport_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian conductance transport).det = ∑ next : V -> V, finiteCRSFOutgoingConductance conductance next * ∑ S : finiteCRSFCycleSupport next, finiteCRSFSupportTransport transport S := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_eq_sum_outgoing_mul_cycleTransport conductance transport

/--
[det_finiteTwistedLaplacian_eq_sum_atomicCycleCoefficients](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_eq_sum_atomicCycleCoefficients_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian conductance transport).det = ∑ next : V -> V, finiteCRSFOutgoingConductance conductance next * ∑ S : finiteCRSFCycleSupport next, ∏ cycle ∈ S.atomicCycles, finiteCRSFAtomicCycleCoefficient transport S cycle := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_eq_sum_atomicCycleCoefficients conductance transport


-- created on 2026-10-23
