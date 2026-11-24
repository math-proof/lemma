module
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Def.Topology.Algebra.PeterWeyl.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
noncomputable section

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

open MeasureTheory

open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction

/--
For a compact Hausdorff topological group and `x ≠ y`, there exist `n>0` and a continuous
homomorphism `ρ : G → Matrix (Fin n) (Fin n) ℂ` with `ρ g ∈ unitaryGroup` for all `g`, `ρ 1 = 1`,
and `ρ x ≠ ρ y`. Source: F. Peter and H. Weyl, Math. Ann. 97 (1927), 737–755; Folland, A Course in
Abstract Harmonic Analysis 2nd ed.; Knapp, Lie Groups Beyond an Introduction 2nd ed.

Proves `Wanted` entry `peter_weyl_point_separation`.
-/
theorem peter_weyl_point_separation
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    {x y : G} (hxy : x ≠ y) :
    ∃ (n : ℕ) (_hn : 0 < n) (ρ : G → Matrix (Fin n) (Fin n) ℂ),
      Continuous ρ ∧
      ρ 1 = 1 ∧
      (∀ g h : G, ρ (g * h) = ρ g * ρ h) ∧
      (∀ g : G, ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
      ρ x ≠ ρ y := by
  borelize G
  have hz : x⁻¹ * y ≠ 1 := by
    intro h
    exact hxy (inv_mul_eq_one.mp h)
  obtain ⟨k, hi, hii⟩ := pwBump (G := G) hz
  obtain ⟨c, hc, v₀, hmem, hne⟩ := pwSeparation (G := G) (x⁻¹ * y) k hi hii
  set E : Submodule ℂ (Lp ℂ 2 (pwHaar G)) :=
    Module.End.eigenspace ((pwS (G := G) k) :
      Module.End ℂ (Lp ℂ 2 (pwHaar G))) c with hEdef
  have hfin : FiniteDimensional ℂ ↥E :=
    ContinuousLinearMap.finite_dimensional_eigenspace (pwS_compact (G := G) k) c hc
  have hinv : ∀ (g : G) (v : Lp ℂ 2 (pwHaar G)),
      v ∈ E → pwTransl (G := G) g v ∈ E := by
    intro g v hv
    exact pwEigen_invariant (G := G) k c g v hv
  have hcont : ∀ (u v : ↥E), Continuous fun g =>
      ⟪(u : Lp ℂ 2 (pwHaar G)), pwTransl (G := G) g (v : Lp ℂ 2 (pwHaar G))⟫ := by
    intro u v
    exact pwEigen_coeff_continuous (G := G) k c hc
      (u : Lp ℂ 2 (pwHaar G)) (v : Lp ℂ 2 (pwHaar G)) v.property
  obtain ⟨n, hn, ρ, hρc, hρ1, hρm, hρu, hρz⟩ :=
    pwRep (G := G) E hfin hinv hcont (x⁻¹ * y) ⟨v₀, hmem⟩ hne
  refine ⟨n, hn, ρ, hρc, hρ1, hρm, hρu, ?_⟩
  intro hxy'
  apply hρz
  rw [hρm x⁻¹ y, ← hxy', ← hρm, inv_mul_cancel, hρ1]

end MathlibExt.Topology.Algebra.PeterWeylWanted
end
