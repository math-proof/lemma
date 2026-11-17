module

public import Mathlib

public section


/--
Mathlib `Submonoid.units_isOpen`
-/
public theorem Set.IsOpenUnits.of.IsOpenSet
  [TopologicalSpace M] [Monoid M]
  {U : Submonoid M}
-- given
  (hU : IsOpen (U : Set M)) :
-- imply
  IsOpen (U.units : Set Mˣ) := by
-- proof
  apply IsOpen.inter
  · exact IsOpen.preimage Units.continuous_val hU
  · exact IsOpen.preimage Units.continuous_coe_inv hU


-- created on 2026-10-24
