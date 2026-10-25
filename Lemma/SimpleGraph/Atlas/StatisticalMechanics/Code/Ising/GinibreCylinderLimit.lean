import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.GinibreCylinderLimit
open Filter Topology StatMech StatMech.Ising


/--
[ginibre_telescope_of_endpoint_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreCylinderLimit.lean)
-/
@[path]
private lemma ginibre_telescope_of_endpoint_tendsto_eq
  {m : Real}
  {D : Real}
-- given
  (top bottom deficit : Nat -> Real)
  (htop : Tendsto top atTop (nhds m))
  (hbottom : Tendsto bottom atTop (nhds (-m)))
  (hdeficit : Tendsto deficit atTop (nhds D))
  (htelescope : forall N, m * (top N - bottom N) <= deficit N) :
-- imply
  2 * m ^ 2 <= D := by
-- proof
  apply StatMech.Ising.ginibre_telescope_of_endpoint_tendsto m top bottom deficit D htop hbottom hdeficit htelescope

/--
[ginibre_telescope_endpoint_le_uniform_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreCylinderLimit.lean)
-/
@[path]
private lemma ginibre_telescope_endpoint_le_uniform_bound_eq
  {m C : Real}
-- given
  (top bottom deficit : Nat -> Real)
  (htop : Tendsto top atTop (nhds m))
  (hbottom : Tendsto bottom atTop (nhds (-m)))
  (htelescope : forall N, m * (top N - bottom N) <= deficit N)
  (hupper : forall N, deficit N <= C) :
-- imply
  2 * m ^ 2 <= C := by
-- proof
  apply StatMech.Ising.ginibre_telescope_endpoint_le_uniform_bound m C top bottom deficit htop hbottom htelescope hupper

/--
[ginibre_widthLimit_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreCylinderLimit.lean)
-/
@[path]
private lemma ginibre_widthLimit_lower_bound_eq
  {M E : Real}
-- given
  (m energy : Nat -> Real)
  (hm : Tendsto m atTop (nhds M))
  (henergy : Tendsto energy atTop (nhds E))
  (hlower : forall L, 2 * (m L) ^ 2 <= energy L) :
-- imply
  2 * M ^ 2 <= E := by
-- proof
  apply StatMech.Ising.ginibre_widthLimit_lower_bound m energy M E hm henergy hlower


-- created on 2026-10-23
