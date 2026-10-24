import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
open StatMech StatMech.FrontierA


/--
[finiteCRSFAmbientAtomicCycleHolonomy_toAtomicCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanProduct.lean)
-/
@[path]
private lemma finiteCRSFAmbientAtomicCycleHolonomy_toAtomicCycle_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (transport : V -> V -> Complex)
  (cycle : {cycle // cycle ∈ S.atomicCycles}) :
-- imply
  finiteCRSFAmbientAtomicCycleHolonomy transport (S.toAtomicCycle cycle) = S.atomicCycleHolonomy transport cycle := by
-- proof
  apply StatMech.FrontierA.finiteCRSFAmbientAtomicCycleHolonomy_toAtomicCycle transport S cycle

/--
[finiteCRSF_prod_localAtomic_eq_prod_ambientAtomic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanProduct.lean)
-/
@[path]
private lemma finiteCRSF_prod_localAtomic_eq_prod_ambientAtomic_eq
  [Fintype V]
  [DecidableEq V]
  {next : V -> V}
  {S : finiteCRSFCycleSupport next}
-- given
  (transport : V -> V -> Complex) :
-- imply
  (∏ cycle ∈ S.atomicCycles, -S.atomicCycleHolonomy transport cycle) = ∏ cycle ∈ S.toAtomicCycles, -finiteCRSFAmbientAtomicCycleHolonomy transport cycle := by
-- proof
  apply StatMech.FrontierA.finiteCRSF_prod_localAtomic_eq_prod_ambientAtomic transport S

/--
[sum_finiteCRSFCycleSupport_eq_prod_one_sub_holonomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanProduct.lean)
-/
@[path]
private lemma sum_finiteCRSFCycleSupport_eq_prod_one_sub_holonomy_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (transport : V -> V -> Complex)
  (next : V -> V) :
-- imply
  (∑ S : finiteCRSFCycleSupport next, ∏ cycle ∈ S.atomicCycles, -S.atomicCycleHolonomy transport cycle) = ∏ cycle : finiteCRSFAtomicCycle next, (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
-- proof
  apply StatMech.FrontierA.sum_finiteCRSFCycleSupport_eq_prod_one_sub_holonomy transport next

/--
[det_finiteTwistedLaplacian_eq_sum_outgoing_mul_formanProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanProduct.lean)
-/
@[path]
private lemma det_finiteTwistedLaplacian_eq_sum_outgoing_mul_formanProduct_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (conductance transport : V -> V -> Complex) :
-- imply
  (finiteTwistedLaplacian conductance transport).det = ∑ next : V -> V, finiteCRSFOutgoingConductance conductance next * ∏ cycle : finiteCRSFAtomicCycle next, (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
-- proof
  apply StatMech.FrontierA.det_finiteTwistedLaplacian_eq_sum_outgoing_mul_formanProduct conductance transport


-- created on 2026-10-23
