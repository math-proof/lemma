/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/NormalFamilies.lean -/


import sympy.atlas.Analysis.Complex.NormalFamilies
import Lemma.Set.IsLocallyUniformlyBoundedOn.of.All_All_LeNorm.Ge_0.IsOpen
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Normal families API checks

Local uniform boundedness from a global bound, bounds on compact subsets, and Montel's and
Vitali's theorems applied to the powers `z ^ n` on the unit disc.
-/

namespace MathlibExtTest.Analysis.Complex.NormalFamilies

open MathlibExt.Analysis.Complex.NormalFamilies Filter Topology

-- The powers `z ^ n` are bounded by `1` on the unit disc.
example : IsLocallyUniformlyBoundedOn (Metric.ball 0 1) (fun n z => z ^ n) :=
  isLocallyUniformlyBoundedOn_of_forall_norm_le Metric.isOpen_ball zero_le_one fun n y hy => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg y) (by simpa using (Metric.mem_ball.mp hy).le)

example {U K : Set ℂ} {F : ℕ → ℂ → ℂ} (hB : IsLocallyUniformlyBoundedOn U F) (hKU : K ⊆ U)
    (hK : IsCompact K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ y ∈ K, ‖F n y‖ ≤ C :=
  hB.exists_bound_of_isCompact hKU hK

-- Montel: some subsequence of `z ^ n` converges locally uniformly on the disc.
example (hB : IsLocallyUniformlyBoundedOn (Metric.ball 0 1) (fun n z => z ^ n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      TendstoLocallyUniformlyOn (fun n z => z ^ φ n) f atTop (Metric.ball 0 1) :=
  montel Metric.isOpen_ball _ (fun n => (differentiable_pow n).differentiableOn) hB

-- Vitali: pointwise convergence on a set with an accumulation point upgrades to locally uniform
-- convergence on the disc.
example (hB : IsLocallyUniformlyBoundedOn (Metric.ball 0 1) (fun n z => z ^ n))
    {S : Set ℂ} (hS : S ⊆ Metric.ball 0 1) (hAcc : AccPt 0 (𝓟 S))
    (hg : ∀ z ∈ S, Tendsto (fun n => z ^ n) atTop (𝓝 0)) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧ (∀ z ∈ S, f z = 0) ∧
      TendstoLocallyUniformlyOn (fun n z => z ^ n) f atTop (Metric.ball 0 1) :=
  vitali Metric.isOpen_ball (convex_ball 0 1).isPreconnected _
    (fun n => (differentiable_pow n).differentiableOn) hB hS
    ⟨0, Metric.mem_ball_self zero_lt_one, hAcc⟩ (fun _ => 0) hg

end MathlibExtTest.Analysis.Complex.NormalFamilies
