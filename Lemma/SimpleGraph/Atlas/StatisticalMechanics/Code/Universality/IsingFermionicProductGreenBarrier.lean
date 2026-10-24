import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicProductGreenBarrier
open StatMech StatMech.Universality


/--
[isingFiniteWeightedLaplacian_mul_of_edgewise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProductGreenBarrier.lean)
-/
@[path]
private lemma isingFiniteWeightedLaplacian_mul_of_edgewise_eq
  [Fintype V]
  {x : V}
-- given
  (conductance : V -> V -> Real)
  (f g : V -> Real)
  (hedge : forall y, Not (conductance x y = 0) -> (f y - f x) * (g y - g x) = 0) :
-- imply
  isingFiniteWeightedLaplacian conductance (fun y => f y * g y) x = f x * isingFiniteWeightedLaplacian conductance g x + g x * isingFiniteWeightedLaplacian conductance f x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLaplacian_mul_of_edgewise conductance f g x hedge

/--
[isingFiniteWeightedLaplacian_mul_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProductGreenBarrier.lean)
-/
@[path]
private lemma isingFiniteWeightedLaplacian_mul_nonpos_eq
  [Fintype V]
  {x : V}
-- given
  (conductance : V -> V -> Real)
  (f g : V -> Real)
  (hedge : forall y, Not (conductance x y = 0) -> (f y - f x) * (g y - g x) = 0)
  (hf : 0 <= f x)
  (hg : 0 <= g x)
  (hfLap : isingFiniteWeightedLaplacian conductance f x <= 0)
  (hgLap : isingFiniteWeightedLaplacian conductance g x <= 0) :
-- imply
  isingFiniteWeightedLaplacian conductance (fun y => f y * g y) x <= 0 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLaplacian_mul_nonpos conductance f g x hedge hf hg hfLap hgLap

/--
[isingFiniteWeightedPointPoissonBarrier_le_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProductGreenBarrier.lean)
-/
@[path]
private lemma isingFiniteWeightedPointPoissonBarrier_le_product_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {source : V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hsource : Not (boundary source))
  (f g : V -> Real)
  (hf_nonneg : forall x, 0 <= f x)
  (hg_nonneg : forall x, 0 <= g x)
  (hden : 0 < f source + g source)
  (hedge : forall x y, Not (conductance x y = 0) -> (f y - f x) * (g y - g x) = 0)
  (hf_super : forall x, Not (boundary x) -> isingFiniteWeightedLaplacian conductance f x <= 0)
  (hg_super : forall x, Not (boundary x) -> isingFiniteWeightedLaplacian conductance g x <= 0)
  (hf_source : isingFiniteWeightedLaplacian conductance f source <= -1)
  (hg_source : isingFiniteWeightedLaplacian conductance g source <= -1) :
-- imply
  forall x, isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit source x <= f x * g x / (f source + g source) := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPointPoissonBarrier_le_product G conductance boundary hconductance hpositive hhit source hsource f g hf_nonneg hg_nonneg hden hedge hf_super hg_super hf_source hg_source

/--
[isingFiniteGraphLaplacian_mul_of_edgewise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProductGreenBarrier.lean)
-/
@[path]
private lemma isingFiniteGraphLaplacian_mul_of_edgewise_eq
  [Fintype V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (f g : V -> Real)
  (hedge : forall y, G.Adj x y -> (f y - f x) * (g y - g x) = 0) :
-- imply
  isingFiniteGraphLaplacian G (fun y => f y * g y) x = f x * isingFiniteGraphLaplacian G g x + g x * isingFiniteGraphLaplacian G f x := by
-- proof
  apply StatMech.Universality.isingFiniteGraphLaplacian_mul_of_edgewise G f g x hedge

/--
[isingFiniteGhostPointPoissonBarrier_le_splitProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProductGreenBarrier.lean)
-/
@[path]
private lemma isingFiniteGhostPointPoissonBarrier_le_splitProduct_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {source : V}
-- given
  (ghostRate rateF rateG : V -> Real)
  (fixed : V -> Prop)
  (hrate : forall x, 0 <= ghostRate x)
  (hsplit : forall x, rateF x + rateG x = ghostRate x)
  (hreach : forall x, exists b, (fixed b \/ 0 < ghostRate b) /\ G.Reachable x b)
  (hsource : Not (fixed source))
  (f g : V -> Real)
  (hf_nonneg : forall x, 0 <= f x)
  (hg_nonneg : forall x, 0 <= g x)
  (hden : 0 < f source + g source)
  (hedge : forall x y, G.Adj x y -> (f y - f x) * (g y - g x) = 0)
  (hf_super : forall x, Not (fixed x) -> isingFiniteGraphLaplacian G f x - rateF x * f x <= 0)
  (hg_super : forall x, Not (fixed x) -> isingFiniteGraphLaplacian G g x - rateG x * g x <= 0)
  (hf_source : isingFiniteGraphLaplacian G f source - rateF source * f source <= -1)
  (hg_source : isingFiniteGraphLaplacian G g source - rateG source * g source <= -1) :
-- imply
  forall x, isingFiniteWeightedPointPoissonBarrier (isingFiniteGhostGraph G ghostRate) (isingFiniteGhostConductance G ghostRate) (isingFiniteGhostBoundaryWith fixed) (isingFiniteGhostConductance_nonneg G ghostRate hrate) (isingFiniteGhostConductance_pos_of_adj G ghostRate) (isingFiniteGhostGraph_reachable_boundaryWith G ghostRate fixed hreach) (some source) (some x) <= f x * g x / (f source + g source) := by
-- proof
  apply StatMech.Universality.isingFiniteGhostPointPoissonBarrier_le_splitProduct G ghostRate rateF rateG fixed hrate hsplit hreach source hsource f g hf_nonneg hg_nonneg hden hedge hf_super hg_super hf_source hg_source


-- created on 2026-10-23
