import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part6
open Finset SimpleGraph StatMech StatMech.Universality


/--
[isingFiniteWeightedLaplacian_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedLaplacian_const_eq
  [Fintype V]
  {conductance : V → V → Real}
  {c : Real}
  {x : V} :
-- imply
  isingFiniteWeightedLaplacian conductance (fun _ ↦ c) x = 0 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLaplacian_const conductance c x

/--
[isingFiniteWeighted_laplacian_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeighted_laplacian_comparison_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
-- given
  (boundary : V → Prop)
  (u h : V → Real)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hboundary : ∀ x, boundary x → u x ≤ h x)
  (hlap : ∀ x, ¬ boundary x → isingFiniteWeightedLaplacian conductance h x ≤ isingFiniteWeightedLaplacian conductance u x) :
-- imply
  ∀ x, u x ≤ h x := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_laplacian_comparison G conductance boundary u h hconductance hpositive hhit hboundary hlap

/--
[isingFiniteWeighted_subharmonic_le_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeighted_subharmonic_le_harmonic_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
-- given
  (boundary : V → Prop)
  (u h : V → Real)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hu : IsingFiniteWeightedSubharmonicOn conductance boundary u)
  (hh : IsingFiniteWeightedHarmonicOn conductance boundary h)
  (hboundary : ∀ x, boundary x → u x ≤ h x) :
-- imply
  ∀ x, u x ≤ h x := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_subharmonic_le_harmonic G conductance boundary u h hconductance hpositive hhit hu hh hboundary

/--
[isingFiniteWeighted_harmonic_le_superharmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeighted_harmonic_le_superharmonic_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
-- given
  (boundary : V → Prop)
  (h u : V → Real)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hh : IsingFiniteWeightedHarmonicOn conductance boundary h)
  (hu : IsingFiniteWeightedSuperharmonicOn conductance boundary u)
  (hboundary : ∀ x, boundary x → h x ≤ u x) :
-- imply
  ∀ x, h x ≤ u x := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_harmonic_le_superharmonic G conductance boundary h u hconductance hpositive hhit hh hu hboundary

/--
[isingFiniteWeighted_subharmonic_le_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeighted_subharmonic_le_const_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {u : V → Real}
  {c : Real}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hu : IsingFiniteWeightedSubharmonicOn conductance boundary u)
  (hboundary : ∀ x, boundary x → u x ≤ c) :
-- imply
  ∀ x, u x ≤ c := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_subharmonic_le_const G conductance boundary u c hconductance hpositive hhit hu hboundary

/--
[isingFiniteWeighted_const_le_superharmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeighted_const_le_superharmonic_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {u : V → Real}
  {c : Real}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hu : IsingFiniteWeightedSuperharmonicOn conductance boundary u)
  (hboundary : ∀ x, boundary x → c ≤ u x) :
-- imply
  ∀ x, c ≤ u x := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_const_le_superharmonic G conductance boundary u c hconductance hpositive hhit hu hboundary

/--
[isingFiniteWeightedLaplacian_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedLaplacian_add_eq
  [Fintype V]
  {conductance : V → V → Real}
  {f g : V → Real}
  {x : V} :
-- imply
  isingFiniteWeightedLaplacian conductance (fun y ↦ f y + g y) x = isingFiniteWeightedLaplacian conductance f x + isingFiniteWeightedLaplacian conductance g x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLaplacian_add conductance f g x

/--
[isingFiniteWeightedLaplacian_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedLaplacian_const_mul_eq
  [Fintype V]
  {conductance : V → V → Real}
  {c : Real}
  {f : V → Real}
  {x : V} :
-- imply
  isingFiniteWeightedLaplacian conductance (fun y ↦ c * f y) x = c * isingFiniteWeightedLaplacian conductance f x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLaplacian_const_mul conductance c f x

/--
[isingFiniteWeightedLaplacian_add_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedLaplacian_add_const_eq
  [Fintype V]
  {conductance : V → V → Real}
  {f : V → Real}
  {c : Real}
  {x : V} :
-- imply
  isingFiniteWeightedLaplacian conductance (fun y ↦ f y + c) x = isingFiniteWeightedLaplacian conductance f x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLaplacian_add_const conductance f c x

/--
[isingFiniteWeightedDirichletOperator_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedDirichletOperator_injective_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  Function.Injective (isingFiniteWeightedDirichletOperator conductance boundary) := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedDirichletOperator_injective G conductance boundary hconductance hpositive hhit

/--
[isingFiniteWeighted_exists_harmonic_extension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeighted_exists_harmonic_extension_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {data : V → Real}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  ∃ harmonic : V → Real, IsingFiniteWeightedHarmonicOn conductance boundary harmonic ∧ ∀ x, boundary x → harmonic x = data x := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_exists_harmonic_extension G conductance boundary hconductance hpositive hhit data

/--
[isingFiniteWeightedDirichletOperator_solve](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedDirichletOperator_solve_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {rhs : V → Real}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  isingFiniteWeightedDirichletOperator conductance boundary (isingFiniteWeightedDirichletSolve G conductance boundary hconductance hpositive hhit rhs) = rhs := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedDirichletOperator_solve G conductance boundary hconductance hpositive hhit rhs

/--
[isingFiniteWeightedPoissonBarrier_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedPoissonBarrier_boundary_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {x : V}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hx : boundary x) :
-- imply
  isingFiniteWeightedPoissonBarrier G conductance boundary hconductance hpositive hhit x = 0 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPoissonBarrier_boundary G conductance boundary hconductance hpositive hhit x hx

/--
[isingFiniteWeightedPoissonBarrier_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedPoissonBarrier_laplacian_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {x : V}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hx : ¬ boundary x) :
-- imply
  isingFiniteWeightedLaplacian conductance (isingFiniteWeightedPoissonBarrier G conductance boundary hconductance hpositive hhit) x = -1 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPoissonBarrier_laplacian G conductance boundary hconductance hpositive hhit x hx

/--
[isingFiniteWeightedPoissonBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedPoissonBarrier_nonneg_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  ∀ x, 0 ≤ isingFiniteWeightedPoissonBarrier G conductance boundary hconductance hpositive hhit x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPoissonBarrier_nonneg G conductance boundary hconductance hpositive hhit

/--
[isingFiniteWeightedPoissonBarrier_le_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedPoissonBarrier_le_bound_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {x : V}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  isingFiniteWeightedPoissonBarrier G conductance boundary hconductance hpositive hhit x ≤ isingFiniteWeightedPoissonBarrierBound G conductance boundary hconductance hpositive hhit := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPoissonBarrier_le_bound G conductance boundary hconductance hpositive hhit x

/--
[isingFiniteWeightedPoissonBarrierBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedPoissonBarrierBound_nonneg_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  0 ≤ isingFiniteWeightedPoissonBarrierBound G conductance boundary hconductance hpositive hhit := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPoissonBarrierBound_nonneg G conductance boundary hconductance hpositive hhit

/--
[isingFiniteWeighted_harmonic_approximation_of_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeighted_harmonic_approximation_of_barrier_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {boundaryError residual barrierBound : Real}
-- given
  (boundary : V → Prop)
  (harmonic target barrier : V → Real)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hharmonic : IsingFiniteWeightedHarmonicOn conductance boundary harmonic)
  (hboundary : ∀ x, boundary x → |harmonic x - target x| ≤ boundaryError)
  (hresidual_nonneg : 0 ≤ residual)
  (hbarrier_nonneg : ∀ x, 0 ≤ barrier x)
  (hbarrier_bound : ∀ x, barrier x ≤ barrierBound)
  (hbarrier_laplacian : ∀ x, ¬ boundary x → isingFiniteWeightedLaplacian conductance barrier x ≤ -1)
  (htarget_residual : ∀ x, ¬ boundary x → |isingFiniteWeightedLaplacian conductance target x| ≤ residual) :
-- imply
  ∀ x, := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_harmonic_approximation_of_barrier G conductance boundary harmonic target barrier boundaryError residual barrierBound hconductance hpositive hhit hharmonic hboundary hresidual_nonneg hbarrier_nonneg hbarrier_bound hbarrier_laplacian htarget_residual

/--
[isingFiniteWeighted_harmonic_approximation_of_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeighted_harmonic_approximation_of_residual_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {boundaryError residual : Real}
-- given
  (boundary : V → Prop)
  (harmonic target : V → Real)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hharmonic : IsingFiniteWeightedHarmonicOn conductance boundary harmonic)
  (hboundary : ∀ x, boundary x → |harmonic x - target x| ≤ boundaryError)
  (hresidual_nonneg : 0 ≤ residual)
  (htarget_residual : ∀ x, ¬ boundary x → |isingFiniteWeightedLaplacian conductance target x| ≤ residual) :
-- imply
  ∀ x, := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_harmonic_approximation_of_residual G conductance boundary harmonic target boundaryError residual hconductance hpositive hhit hharmonic hboundary hresidual_nonneg htarget_residual

/--
[isingFiniteWeightedSpatialResidualPotential_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedSpatialResidualPotential_boundary_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {residual : V → Real}
  {x : V}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hx : boundary x) :
-- imply
  isingFiniteWeightedSpatialResidualPotential G conductance boundary hconductance hpositive hhit residual x = 0 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedSpatialResidualPotential_boundary G conductance boundary hconductance hpositive hhit residual x hx

/--
[isingFiniteWeightedSpatialResidualPotential_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedSpatialResidualPotential_laplacian_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {residual : V → Real}
  {x : V}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hx : ¬ boundary x) :
-- imply
  isingFiniteWeightedLaplacian conductance (isingFiniteWeightedSpatialResidualPotential G conductance boundary hconductance hpositive hhit residual) x = -residual x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedSpatialResidualPotential_laplacian G conductance boundary hconductance hpositive hhit residual x hx

/--
[isingFiniteWeightedSpatialResidualPotential_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeightedSpatialResidualPotential_nonneg_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {residual : V → Real}
-- given
  (boundary : V → Prop)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hresidual : ∀ x, 0 ≤ residual x) :
-- imply
  ∀ x, 0 ≤ isingFiniteWeightedSpatialResidualPotential G conductance boundary hconductance hpositive hhit residual x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedSpatialResidualPotential_nonneg G conductance boundary hconductance hpositive hhit residual hresidual

/--
[isingFiniteWeighted_harmonic_approximation_of_spatial_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteWeighted_harmonic_approximation_of_spatial_residual_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {conductance : V → V → Real}
  {boundaryError : Real}
  {residual : V → Real}
-- given
  (boundary : V → Prop)
  (harmonic target : V → Real)
  (hconductance : ∀ x y, 0 ≤ conductance x y)
  (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hharmonic : IsingFiniteWeightedHarmonicOn conductance boundary harmonic)
  (hboundary : ∀ x, boundary x → |harmonic x - target x| ≤ boundaryError)
  (hresidual_nonneg : ∀ x, 0 ≤ residual x)
  (htarget_residual : ∀ x, ¬ boundary x → |isingFiniteWeightedLaplacian conductance target x| ≤ residual x) :
-- imply
  ∀ x, := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_harmonic_approximation_of_spatial_residual G conductance boundary harmonic target boundaryError residual hconductance hpositive hhit hharmonic hboundary hresidual_nonneg htarget_residual


-- created on 2026-10-23
