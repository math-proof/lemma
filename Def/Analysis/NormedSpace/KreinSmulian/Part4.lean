/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Data.List.GetD
public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Theorem.Analysis.NormedSpace.KreinSmulian.Part3

@[expose] public section

namespace FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open scoped ComplexConjugate ZeroAtInfty

/-- Indicator of a singleton in `C₀(ℕ × ℕ, ℝ)`. -/
noncomputable def ks_ind (p : ℕ × ℕ) : C₀(ℕ × ℕ, ℝ) :=
  ZeroAtInftyContinuousMap.mk
    ⟨Set.indicator {p} (fun _ => (1 : ℝ)), continuous_of_discreteTopology⟩ (by
    rw [Filter.cocompact_eq_cofinite]
    have hev : ∀ᶠ q : ℕ × ℕ in Filter.cofinite,
        (0 : ℝ) = Set.indicator ({p} : Set (ℕ × ℕ)) (fun _ => (1 : ℝ)) q := by
      rw [Filter.eventually_cofinite]
      apply Set.Finite.subset (Finset.finite_toSet {p})
      intro q hq
      simp only [Set.mem_ofPred_eq] at hq
      rw [Finset.mem_coe, Finset.mem_singleton]
      by_contra hcon
      have hmem : q ∉ ({p} : Set (ℕ × ℕ)) := by
        simpa only [Set.mem_singleton_iff] using hcon
      have h0q : Set.indicator ({p} : Set (ℕ × ℕ)) (fun _ => (1 : ℝ)) q = 0 :=
        Set.indicator_of_notMem hmem _
      exact hq h0q.symm
    exact Filter.Tendsto.congr' hev tendsto_const_nhds)

end FunctionalAnalysis.BanachSpaceWanted
