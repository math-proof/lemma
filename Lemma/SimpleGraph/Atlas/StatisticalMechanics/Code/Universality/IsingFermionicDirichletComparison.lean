import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
open Finset SimpleGraph StatMech StatMech.Universality


/--
[isingFiniteGraphLaplacian_add_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraphLaplacian_add_const_eq
  [Fintype V]
  {G : SimpleGraph V}
  {f : V → ℝ}
  {c : ℝ}
  {x : V} :
-- imply
  isingFiniteGraphLaplacian G (fun y ↦ f y + c) x = isingFiniteGraphLaplacian G f x := by
-- proof
  apply StatMech.Universality.isingFiniteGraphLaplacian_add_const G f c x

/--
[isingFiniteGraphLaplacian_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraphLaplacian_add_eq
  [Fintype V]
  {G : SimpleGraph V}
  {f g : V → ℝ}
  {x : V} :
-- imply
  isingFiniteGraphLaplacian G (fun y ↦ f y + g y) x = isingFiniteGraphLaplacian G f x + isingFiniteGraphLaplacian G g x := by
-- proof
  apply StatMech.Universality.isingFiniteGraphLaplacian_add G f g x

/--
[isingFiniteGraphLaplacian_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraphLaplacian_const_mul_eq
  [Fintype V]
  {G : SimpleGraph V}
  {c : ℝ}
  {f : V → ℝ}
  {x : V} :
-- imply
  isingFiniteGraphLaplacian G (fun y ↦ c * f y) x = c * isingFiniteGraphLaplacian G f x := by
-- proof
  apply StatMech.Universality.isingFiniteGraphLaplacian_const_mul G c f x

/--
[IsingFiniteGraphHarmonicOn.add_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma add_const_eq
  [Fintype V]
  {G : SimpleGraph V}
  {boundary : V → Prop}
  {f : V → ℝ}
  {c : ℝ}
-- given
  (hf : IsingFiniteGraphHarmonicOn G boundary f) :
-- imply
  IsingFiniteGraphHarmonicOn G boundary (fun x ↦ f x + c) := by
-- proof
  apply StatMech.Universality.IsingFiniteGraphHarmonicOn.add_const hf c

/--
[isingFiniteGraph_laplacian_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraph_laplacian_comparison_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
-- given
  (boundary : V → Prop)
  (u h : V → ℝ)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hboundary : ∀ x, boundary x → u x ≤ h x)
  (hlap : ∀ x, ¬ boundary x → isingFiniteGraphLaplacian G h x ≤ isingFiniteGraphLaplacian G u x) :
-- imply
  ∀ x, u x ≤ h x := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_laplacian_comparison G boundary u h hhit hboundary hlap

/--
[isingFiniteGraph_subharmonic_le_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraph_subharmonic_le_harmonic_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
-- given
  (boundary : V → Prop)
  (u h : V → ℝ)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hu : IsingFiniteGraphSubharmonicOn G boundary u)
  (hh : IsingFiniteGraphHarmonicOn G boundary h)
  (hboundary : ∀ x, boundary x → u x ≤ h x) :
-- imply
  ∀ x, u x ≤ h x := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_subharmonic_le_harmonic G boundary u h hhit hu hh hboundary

/--
[isingFiniteGraph_harmonic_le_superharmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraph_harmonic_le_superharmonic_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
-- given
  (boundary : V → Prop)
  (h u : V → ℝ)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hh : IsingFiniteGraphHarmonicOn G boundary h)
  (hu : IsingFiniteGraphSuperharmonicOn G boundary u)
  (hboundary : ∀ x, boundary x → h x ≤ u x) :
-- imply
  ∀ x, h x ≤ u x := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_harmonic_le_superharmonic G boundary h u hhit hh hu hboundary

/--
[isingFiniteGraph_harmonic_boundary_stability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraph_harmonic_boundary_stability_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {u v : V → ℝ}
  {eps : ℝ}
-- given
  (boundary : V → Prop)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hu : IsingFiniteGraphHarmonicOn G boundary u)
  (hv : IsingFiniteGraphHarmonicOn G boundary v)
  (hboundary : ∀ x, boundary x → |u x - v x| ≤ eps) :
-- imply
  ∀ x, := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_harmonic_boundary_stability G boundary u v eps hhit hu hv hboundary

/--
[isingFiniteGraphDirichletOperator_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraphDirichletOperator_injective_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
-- given
  (boundary : V → Prop)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  Function.Injective (isingFiniteGraphDirichletOperator G boundary) := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDirichletOperator_injective G boundary hhit

/--
[isingFiniteGraph_exists_harmonic_extension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraph_exists_harmonic_extension_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {data : V → ℝ}
-- given
  (boundary : V → Prop)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  ∃ harmonic : V → ℝ, IsingFiniteGraphHarmonicOn G boundary harmonic ∧ ∀ x, boundary x → harmonic x = data x := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_exists_harmonic_extension G boundary hhit data

/--
[isingFiniteGraphDirichletOperator_solve](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraphDirichletOperator_solve_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {rhs : V → ℝ}
-- given
  (boundary : V → Prop)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  isingFiniteGraphDirichletOperator G boundary (isingFiniteGraphDirichletSolve G boundary hhit rhs) = rhs := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDirichletOperator_solve G boundary hhit rhs

/--
[isingFiniteGraphPoissonBarrier_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraphPoissonBarrier_boundary_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (boundary : V → Prop)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hx : boundary x) :
-- imply
  isingFiniteGraphPoissonBarrier G boundary hhit x = 0 := by
-- proof
  apply StatMech.Universality.isingFiniteGraphPoissonBarrier_boundary G boundary hhit x hx

/--
[isingFiniteGraphPoissonBarrier_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraphPoissonBarrier_laplacian_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (boundary : V → Prop)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hx : ¬ boundary x) :
-- imply
  isingFiniteGraphLaplacian G (isingFiniteGraphPoissonBarrier G boundary hhit) x = -1 := by
-- proof
  apply StatMech.Universality.isingFiniteGraphPoissonBarrier_laplacian G boundary hhit x hx

/--
[isingFiniteGraphPoissonBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraphPoissonBarrier_nonneg_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
-- given
  (boundary : V → Prop)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  ∀ x, 0 ≤ isingFiniteGraphPoissonBarrier G boundary hhit x := by
-- proof
  apply StatMech.Universality.isingFiniteGraphPoissonBarrier_nonneg G boundary hhit

/--
[isingFiniteGraphPoissonBarrier_le_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraphPoissonBarrier_le_bound_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (boundary : V → Prop)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
-- imply
  isingFiniteGraphPoissonBarrier G boundary hhit x ≤ isingFiniteGraphPoissonBarrierBound G boundary hhit := by
-- proof
  apply StatMech.Universality.isingFiniteGraphPoissonBarrier_le_bound G boundary hhit x

/--
[isingFiniteGraph_subsuperharmonic_boundary_stability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraph_subsuperharmonic_boundary_stability_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {eps : ℝ}
-- given
  (boundary : V → Prop)
  (u h : V → ℝ)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (husub : IsingFiniteGraphSubharmonicOn G boundary u)
  (husuper : IsingFiniteGraphSuperharmonicOn G boundary u)
  (hh : IsingFiniteGraphHarmonicOn G boundary h)
  (hboundary : ∀ x, boundary x → |u x - h x| ≤ eps) :
-- imply
  ∀ x, := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_subsuperharmonic_boundary_stability G boundary u h eps hhit husub husuper hh hboundary

/--
[isingFiniteGraph_harmonic_approximation_of_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraph_harmonic_approximation_of_barrier_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {boundaryError residual barrierBound : ℝ}
-- given
  (boundary : V → Prop)
  (harmonic target barrier : V → ℝ)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hharmonic : IsingFiniteGraphHarmonicOn G boundary harmonic)
  (hboundary : ∀ x, boundary x → |harmonic x - target x| ≤ boundaryError)
  (hresidual_nonneg : 0 ≤ residual)
  (hbarrier_nonneg : ∀ x, 0 ≤ barrier x)
  (hbarrier_bound : ∀ x, barrier x ≤ barrierBound)
  (hbarrier_laplacian : ∀ x, ¬ boundary x → isingFiniteGraphLaplacian G barrier x ≤ -1)
  (htarget_residual : ∀ x, ¬ boundary x → |isingFiniteGraphLaplacian G target x| ≤ residual) :
-- imply
  ∀ x, := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_harmonic_approximation_of_barrier G boundary harmonic target barrier boundaryError residual barrierBound hhit hharmonic hboundary hresidual_nonneg hbarrier_nonneg hbarrier_bound hbarrier_laplacian htarget_residual

/--
[isingFiniteGraph_harmonic_approximation_of_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean)
-/
@[path]
private lemma isingFiniteGraph_harmonic_approximation_of_residual_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {boundaryError residual : ℝ}
-- given
  (boundary : V → Prop)
  (harmonic target : V → ℝ)
  (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
  (hharmonic : IsingFiniteGraphHarmonicOn G boundary harmonic)
  (hboundary : ∀ x, boundary x → |harmonic x - target x| ≤ boundaryError)
  (hresidual_nonneg : 0 ≤ residual)
  (htarget_residual : ∀ x, ¬ boundary x → |isingFiniteGraphLaplacian G target x| ≤ residual) :
-- imply
  ∀ x, := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_harmonic_approximation_of_residual G boundary harmonic target boundaryError residual hhit hharmonic hboundary hresidual_nonneg htarget_residual


-- created on 2026-10-23
