import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM14.WaveEnergy.Part3
open MeasureTheory Set Finset Classical CM14


namespace CM14

/--
[partialDeriv_eq_fderiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma partialDeriv_eq_fderiv
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {μ : Fin (n + 1)}
-- given
  (hφ : DifferentiableAt ℝ φ p) :
-- imply
  partialDeriv φ μ p = fderiv ℝ φ p (basisDir μ) := by
-- proof
  simp only [partialDeriv, basisDir]
  split_ifs with h
  · have hcomp : HasFDerivAt (fun s => φ (s, p.2))
    (fderiv ℝ φ p ∘L ContinuousLinearMap.inl ℝ ℝ (Fin n → ℝ)) p.1 :=
    hφ.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)
    rw [hcomp.fderiv]; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  · have hcomp : HasFDerivAt (fun y => φ (p.1, y))
    (fderiv ℝ φ p ∘L ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) p.2 :=
    hφ.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
    rw [hcomp.fderiv]; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

end CM14

namespace CM14

/--
[EMT_product_rule_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma EMT_product_rule_expansion
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {ν : Fin (n + 1)}
-- given
  (_hφ : ContDiff ℝ 2 φ) :
-- imply
  divEnergyMomentumTensor φ p ν = waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) + EMT_remainder φ p ν := by
-- proof
  unfold EMT_remainder
  ring

end CM14

namespace CM14

/--
[minkowskiInverse_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma minkowskiInverse_symm
  {n : ℕ}
  {μ ν : Fin (n + 1)} :
-- imply
  minkowskiInverse n μ ν = minkowskiInverse n ν μ := by
-- proof
  simp only [minkowskiInverse, waveMinkowskiMetric]
  split_ifs with h1 h2 h3 <;> simp_all [eq_comm]

end CM14

namespace CM14

/--
[triple_sum_swap_13](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma triple_sum_swap_13
  {N : ℕ}
  {f : Fin N → Fin N → Fin N → ℝ} :
-- imply
  ∑ μ : Fin N, ∑ α : Fin N, ∑ β : Fin N, f μ α β = ∑ μ : Fin N, ∑ α : Fin N, ∑ β : Fin N, f β α μ := by
-- proof
  have step1 : ∑ μ : Fin N, ∑ α : Fin N, ∑ β : Fin N, f μ α β =
    ∑ α : Fin N, ∑ μ : Fin N, ∑ β : Fin N, f μ α β := Finset.sum_comm
  have step2 : ∑ α : Fin N, ∑ μ : Fin N, ∑ β : Fin N, f μ α β =
    ∑ α : Fin N, ∑ β : Fin N, ∑ μ : Fin N, f μ α β := by
    congr 1; ext α; exact Finset.sum_comm
  have step3 : ∑ α : Fin N, ∑ β : Fin N, ∑ μ : Fin N, f μ α β =
    ∑ β : Fin N, ∑ α : Fin N, ∑ μ : Fin N, f μ α β := Finset.sum_comm
  linarith

end CM14

namespace CM14

/--
[partialDeriv_schwarz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma partialDeriv_schwarz
  {n : ℕ}
  {φ : WaveScalarField n}
  {μ β : Fin (n + 1)}
  {p : WaveSpacetime n}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  partialDeriv (fun q => partialDeriv φ β q) μ p = partialDeriv (fun q => partialDeriv φ μ q) β p := by
-- proof
  have hDiff : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have heq_β : (fun q => partialDeriv φ β q) = (fun q => fderiv ℝ φ q (basisDir β)) := by
    ext q; exact partialDeriv_eq_fderiv φ (hDiff q) β
  have heq_μ : (fun q => partialDeriv φ μ q) = (fun q => fderiv ℝ φ q (basisDir μ)) := by
    ext q; exact partialDeriv_eq_fderiv φ (hDiff q) μ
  rw [heq_β, heq_μ]
  have hDiff_fderiv : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (by norm_num)).differentiable one_ne_zero
  have hDiff_apply_β : Differentiable ℝ (fun q => fderiv ℝ φ q (basisDir β)) :=
    (ContinuousLinearMap.apply ℝ ℝ (basisDir β)).differentiable.comp hDiff_fderiv
  have hDiff_apply_μ : Differentiable ℝ (fun q => fderiv ℝ φ q (basisDir μ)) :=
    (ContinuousLinearMap.apply ℝ ℝ (basisDir μ)).differentiable.comp hDiff_fderiv
  rw [partialDeriv_eq_fderiv _ (hDiff_apply_β p) μ,
    partialDeriv_eq_fderiv _ (hDiff_apply_μ p) β]
  have key_β : fderiv ℝ (fun q => fderiv ℝ φ q (basisDir β)) p (basisDir μ) =
    fderiv ℝ (fderiv ℝ φ) p (basisDir μ) (basisDir β) := by
    have h1 : fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ (basisDir β)) ∘ (fderiv ℝ φ)) p =
      (ContinuousLinearMap.apply ℝ ℝ (basisDir β)).comp (fderiv ℝ (fderiv ℝ φ) p) :=
      (ContinuousLinearMap.apply ℝ ℝ (basisDir β)).hasFDerivAt.comp p
        (hDiff_fderiv p).hasFDerivAt |>.fderiv
    simp only [Function.comp_def] at h1
    rw [show (fun q => fderiv ℝ φ q (basisDir β)) =
      (fun q => (ContinuousLinearMap.apply ℝ ℝ (basisDir β)) (fderiv ℝ φ q)) from rfl, h1]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  have key_μ : fderiv ℝ (fun q => fderiv ℝ φ q (basisDir μ)) p (basisDir β) =
    fderiv ℝ (fderiv ℝ φ) p (basisDir β) (basisDir μ) := by
    have h1 : fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ (basisDir μ)) ∘ (fderiv ℝ φ)) p =
      (ContinuousLinearMap.apply ℝ ℝ (basisDir μ)).comp (fderiv ℝ (fderiv ℝ φ) p) :=
      (ContinuousLinearMap.apply ℝ ℝ (basisDir μ)).hasFDerivAt.comp p
        (hDiff_fderiv p).hasFDerivAt |>.fderiv
    simp only [Function.comp_def] at h1
    rw [show (fun q => fderiv ℝ φ q (basisDir μ)) =
      (fun q => (ContinuousLinearMap.apply ℝ ℝ (basisDir μ)) (fderiv ℝ φ q)) from rfl, h1]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [key_β, key_μ]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (basisDir μ) (basisDir β)

end CM14

namespace CM14

/--
[partialDeriv_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma partialDeriv_mul
  {n : ℕ}
  {f g : WaveScalarField n}
  {μ : Fin (n + 1)}
  {p : WaveSpacetime n}
-- given
  (hf : DifferentiableAt ℝ f p)
  (hg : DifferentiableAt ℝ g p) :
-- imply
  partialDeriv (fun q => f q * g q) μ p = partialDeriv f μ p * g p + f p * partialDeriv g μ p := by
-- proof
  have hfg : DifferentiableAt ℝ (fun q => f q * g q) p := hf.mul hg
  rw [partialDeriv_eq_fderiv _ hfg μ, partialDeriv_eq_fderiv f hf μ, partialDeriv_eq_fderiv g hg μ]
  have hmul : HasFDerivAt (f * g)
    (f p • fderiv ℝ g p + g p • fderiv ℝ f p) p :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [show fderiv ℝ (fun q => f q * g q) p = fderiv ℝ (f * g) p from rfl]
  rw [hmul.fderiv]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  ring

end CM14

namespace CM14

/--
[partialDeriv_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma partialDeriv_const_mul
  {n : ℕ}
  {c : ℝ}
  {f : WaveScalarField n}
  {μ : Fin (n + 1)}
  {p : WaveSpacetime n}
-- given
  (hf : DifferentiableAt ℝ f p) :
-- imply
  partialDeriv (fun q => c * f q) μ p = c * partialDeriv f μ p := by
-- proof
  have hcf : DifferentiableAt ℝ (fun q => c * f q) p := hf.const_mul c
  rw [partialDeriv_eq_fderiv _ hcf μ, partialDeriv_eq_fderiv f hf μ]
  have hmul : HasFDerivAt (fun q => c * f q) (c • fderiv ℝ f p) p :=
    hf.hasFDerivAt.const_mul c
  rw [hmul.fderiv]
  simp [ContinuousLinearMap.smul_apply]

end CM14

namespace CM14

/--
[partialDeriv_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma partialDeriv_finset_sum
  {n : ℕ}
  {s : Finset ι}
  {f : ι → WaveScalarField n}
  {μ : Fin (n + 1)}
  {p : WaveSpacetime n}
-- given
  (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) p) :
-- imply
  partialDeriv (fun q => ∑ i ∈ s, f i q) μ p = ∑ i ∈ s, partialDeriv (f i) μ p := by
-- proof
  rw [partialDeriv_eq_fderiv _ (DifferentiableAt.fun_sum hf) μ,
    fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← partialDeriv_eq_fderiv _ (hf i hi) μ]

end CM14

namespace CM14

/--
[partialDeriv_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma partialDeriv_sub
  {n : ℕ}
  {f g : WaveScalarField n}
  {μ : Fin (n + 1)}
  {p : WaveSpacetime n}
-- given
  (hf : DifferentiableAt ℝ f p)
  (hg : DifferentiableAt ℝ g p) :
-- imply
  partialDeriv (fun q => f q - g q) μ p = partialDeriv f μ p - partialDeriv g μ p := by
-- proof
  have heq : (fun q => f q - g q) = f - g := rfl
  rw [heq, partialDeriv_eq_fderiv _ (hf.sub hg) μ, fderiv_sub hf hg,
    ContinuousLinearMap.sub_apply,
    ← partialDeriv_eq_fderiv _ hf μ, ← partialDeriv_eq_fderiv _ hg μ]

end CM14

namespace CM14

/--
[divEMT_potential_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma divEMT_potential_expansion
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {μ : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  partialDeriv (fun q => ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) μ p = ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n α β * (partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p + partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
-- proof
  have hDiff : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hpd_diff : ∀ α, Differentiable ℝ (fun q => partialDeriv φ α q) := by
    intro α
    have heq : (fun q => partialDeriv φ α q) = (fun q => fderiv ℝ φ q (basisDir α)) := by
      ext q; exact partialDeriv_eq_fderiv φ (hDiff q) α
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ ℝ (basisDir α)).differentiable.comp
      ((hφ.fderiv_right (by norm_num)).differentiable one_ne_zero)
  have hpd : ∀ α, DifferentiableAt ℝ (fun q => partialDeriv φ α q) p :=
    fun α => (hpd_diff α) p
  have hprod : ∀ (α β : Fin (n + 1)),
    DifferentiableAt ℝ (fun q => partialDeriv φ α q * partialDeriv φ β q) p :=
    fun α β => (hpd α).mul (hpd β)
  have hterm : ∀ (α β : Fin (n + 1)),
    DifferentiableAt ℝ (fun q => minkowskiInverse n α β *
      partialDeriv φ α q * partialDeriv φ β q) p := by
    intro α β
    exact ((hpd α).const_mul _).mul (hpd β)
  have hinner : ∀ (α : Fin (n + 1)),
    DifferentiableAt ℝ (fun q => ∑ β : Fin (n + 1),
      minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) p := by
    intro α
    exact DifferentiableAt.fun_sum (fun β _ => hterm α β)
  rw [partialDeriv_finset_sum Finset.univ
    (fun α q => ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q)
    μ p (fun α _ => hinner α)]
  apply Finset.sum_congr rfl
  intro α _
  rw [partialDeriv_finset_sum Finset.univ
    (fun β q => minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q)
    μ p (fun β _ => hterm α β)]
  apply Finset.sum_congr rfl
  intro β _
  have hassoc : (fun q => minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) =
    (fun q => minkowskiInverse n α β * (partialDeriv φ α q * partialDeriv φ β q)) := by
    ext q; ring
  rw [hassoc]
  rw [partialDeriv_const_mul _ _ _ _ (hprod α β)]
  rw [partialDeriv_mul _ _ _ _ (hpd α) (hpd β)]

end CM14

namespace CM14

/--
[divEMT_explicit_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma divEMT_explicit_expansion
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {ν : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  divEnergyMomentumTensor φ p ν = waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) + (∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ α * minkowskiInverse n ν β * partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) + (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ ν * minkowskiInverse n α β * partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) + (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ ν * minkowskiInverse n α β * partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
-- proof
  have hDiff : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hpd_diff : ∀ α, Differentiable ℝ (fun q => partialDeriv φ α q) := by
    intro α
    have heq : (fun q => partialDeriv φ α q) = (fun q => fderiv ℝ φ q (basisDir α)) := by
      ext q; exact partialDeriv_eq_fderiv φ (hDiff q) α
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ ℝ (basisDir α)).differentiable.comp
      ((hφ.fderiv_right (by norm_num)).differentiable one_ne_zero)
  have hpd : ∀ α, DifferentiableAt ℝ (fun q => partialDeriv φ α q) p :=
    fun α => (hpd_diff α) p
  have hprod : ∀ (γ δ : Fin (n + 1)),
    DifferentiableAt ℝ (fun q => partialDeriv φ γ q * partialDeriv φ δ q) p :=
    fun γ δ => (hpd γ).mul (hpd δ)
  have hpot : DifferentiableAt ℝ (fun q => ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
    minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) p := by
    apply DifferentiableAt.fun_sum; intro α _
    apply DifferentiableAt.fun_sum; intro β _
    exact ((hpd α).const_mul _).mul (hpd β)
  have hpot_c : ∀ (γ δ : Fin (n + 1)),
    DifferentiableAt ℝ (fun q => 1 / 2 * waveMinkowskiMetric n γ δ *
      ∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) p := by
    intro γ δ
    have : (fun q => 1 / 2 * waveMinkowskiMetric n γ δ *
      ∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) =
      (fun q => (1 / 2 * waveMinkowskiMetric n γ δ) *
        (∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q)) := by
      ext q; ring
    rw [this]; exact hpot.const_mul _
  have hEMT : ∀ (γ δ : Fin (n + 1)),
    DifferentiableAt ℝ (fun q => energyMomentumTensor φ q γ δ) p := by
    intro γ δ; unfold energyMomentumTensor; exact (hprod γ δ).sub (hpot_c γ δ)
  have hcEMT : ∀ (μ γ δ : Fin (n + 1)),
    DifferentiableAt ℝ (fun q => minkowskiInverse n μ γ * minkowskiInverse n ν δ *
      energyMomentumTensor φ q γ δ) p := by
    intro μ γ δ; exact (hEMT γ δ).const_mul _
  have hInnerSum : ∀ (μ γ : Fin (n + 1)),
    DifferentiableAt ℝ (fun q => ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n ν δ *
        energyMomentumTensor φ q γ δ) p := by
    intro μ γ; exact DifferentiableAt.fun_sum (fun δ _ => hcEMT μ γ δ)
  unfold divEnergyMomentumTensor
  conv_lhs =>
    arg 2; ext μ
    rw [partialDeriv_finset_sum Finset.univ _ μ p (fun γ _ => hInnerSum μ γ)]
    arg 2; ext γ
    rw [partialDeriv_finset_sum Finset.univ _ μ p (fun δ _ => hcEMT μ γ δ)]
    arg 2; ext δ
    rw [show (fun q => minkowskiInverse n μ γ * minkowskiInverse n ν δ *
      energyMomentumTensor φ q γ δ) =
      (fun q => (minkowskiInverse n μ γ * minkowskiInverse n ν δ) *
        energyMomentumTensor φ q γ δ) from by ext q; ring]
    rw [partialDeriv_const_mul _ _ μ p (hEMT γ δ)]
  simp only [energyMomentumTensor]
  conv_lhs =>
    arg 2; ext μ; arg 2; ext γ; arg 2; ext δ
    rw [show (fun q => partialDeriv φ γ q * partialDeriv φ δ q -
      1 / 2 * waveMinkowskiMetric n γ δ *
      ∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q) =
      (fun q => (fun q => partialDeriv φ γ q * partialDeriv φ δ q) q -
        (fun q => (1 / 2 * waveMinkowskiMetric n γ δ) *
        (∑ α, ∑ β, minkowskiInverse n α β * partialDeriv φ α q * partialDeriv φ β q)) q)
      from by ext q; ring]
    rw [partialDeriv_sub _ _ μ p (hprod γ δ) (hpot.const_mul _)]
    rw [partialDeriv_mul (fun q => partialDeriv φ γ q) (fun q => partialDeriv φ δ q) μ p (hpd γ) (hpd δ)]
    rw [partialDeriv_const_mul _ _ μ p hpot]
    rw [divEMT_potential_expansion φ hφ p μ]
  have hwaveOp : waveOp φ p = ∑ μ : Fin (n + 1),
    minkowskiInverse n μ μ * partialDeriv (fun q => partialDeriv φ μ q) μ p := by
    simp only [waveOp]
    rw [Fin.sum_univ_succ]
    simp only [minkowskiInverse, waveMinkowskiMetric, Fin.val_zero, if_true]
    have h0 : partialDeriv (fun q => partialDeriv φ 0 q) 0 p =
      fderiv ℝ (fun s => fderiv ℝ (fun r => φ (r, p.2)) s 1) p.1 1 := by
      simp [partialDeriv]
    rw [h0]; congr 1; · ring
    apply Finset.sum_congr rfl; intro i _
    have hsucc : ¬ (Fin.succ i : Fin (n + 1)).val = 0 := by simp [Fin.val_succ]
    simp only [hsucc, ite_false]
    have hpd_ss : partialDeriv (fun q => partialDeriv φ i.succ q) i.succ p =
      fderiv ℝ (fun y => fderiv ℝ (fun z => φ (p.1, z)) y (Pi.single i 1)) p.2 (Pi.single i 1) := by
      simp only [partialDeriv, Fin.val_succ]; simp
    rw [hpd_ss]; ring
  have hdiag : ∀ (μ : Fin (n + 1)) (f : Fin (n + 1) → ℝ),
    ∑ γ : Fin (n + 1), minkowskiInverse n μ γ * f γ =
      minkowskiInverse n μ μ * f μ := by
    intro μ f
    simp only [minkowskiInverse, waveMinkowskiMetric]
    rw [Finset.sum_eq_single μ]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ μ) h
  have hmetric_contract : ∀ (μ δ : Fin (n + 1)),
    ∑ γ : Fin (n + 1), minkowskiInverse n μ γ * waveMinkowskiMetric n γ δ =
      if μ = δ then 1 else 0 := by
    intro μ δ
    simp only [minkowskiInverse, waveMinkowskiMetric]
    rw [Finset.sum_eq_single μ]
    · simp only [ite_mul, one_mul, neg_mul, if_true]
      split_ifs <;> simp_all <;> omega
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ μ) h
  set dpd := fun (α μ : Fin (n + 1)) => partialDeriv (fun q => partialDeriv φ α q) μ p with dpd_def
  set pd := fun (α : Fin (n + 1)) => partialDeriv φ α p with pd_def
  set m := fun (μ γ : Fin (n + 1)) => minkowskiInverse n μ γ with m_def
  set met := fun (γ δ : Fin (n + 1)) => waveMinkowskiMetric n γ δ with met_def
  have hLHS_split : ∀ (μ γ δ : Fin (n + 1)),
    m μ γ * m ν δ *
      (dpd γ μ * pd δ + pd γ * dpd δ μ -
        1 / 2 * met γ δ *
          ∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) =
    m μ γ * m ν δ * dpd γ μ * pd δ +
    m μ γ * m ν δ * pd γ * dpd δ μ -
    m μ γ * m ν δ * (1 / 2 * met γ δ) *
      (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) := by
    intro μ γ δ; ring
  conv_lhs => arg 2; ext μ; arg 2; ext γ; arg 2; ext δ; rw [hLHS_split μ γ δ]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hkin1 : ∑ μ : Fin (n + 1), ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
    m μ γ * m ν δ * dpd γ μ * pd δ =
    waveOp φ p * ∑ α, m ν α * pd α := by
    have : ∀ μ, ∑ γ, ∑ δ, m μ γ * m ν δ * dpd γ μ * pd δ =
      (∑ γ, m μ γ * dpd γ μ) * (∑ δ, m ν δ * pd δ) := by
      intro μ
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro γ _
      simp_rw [show ∀ (δ : Fin (n + 1)),
        m μ γ * m ν δ * dpd γ μ * pd δ = (m μ γ * dpd γ μ) * (m ν δ * pd δ) from
        by intro δ; ring]
      rw [← Finset.mul_sum]
    simp_rw [this]
    rw [← Finset.sum_mul]
    congr 1
    conv_lhs => arg 2; ext μ; rw [hdiag μ (fun γ => dpd γ μ)]
    exact hwaveOp.symm
  have hkin2 : ∑ μ : Fin (n + 1), ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
    m μ γ * m ν δ * pd γ * dpd δ μ =
    ∑ μ, ∑ α, ∑ β, m μ α * m ν β * pd α * dpd β μ := by
    apply Finset.sum_congr rfl; intro μ _
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    ring
  have hpot_simp : ∑ μ : Fin (n + 1), ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
    m μ γ * m ν δ * (1 / 2 * met γ δ) *
      (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) =
    1 / 2 * ∑ μ, m ν μ *
      (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) := by
    simp_rw [show ∀ (μ γ δ : Fin (n + 1)) (x : ℝ),
      m μ γ * m ν δ * (1 / 2 * met γ δ) * x =
      1 / 2 * (m μ γ * met γ δ) * m ν δ * x from by intros; ring]
    rw [show (∑ μ : Fin (n + 1), ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      1 / 2 * (m μ γ * met γ δ) * m ν δ *
        (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ))) =
      1 / 2 * ∑ μ, ∑ γ, ∑ δ,
        (m μ γ * met γ δ) * m ν δ *
          (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro μ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro γ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro δ _
      ring]
    congr 1
    apply Finset.sum_congr rfl; intro μ _
    rw [Finset.sum_comm]
    simp_rw [show ∀ (γ δ : Fin (n + 1)) (x : ℝ),
      m μ γ * met γ δ * m ν δ * x = (m μ γ * met γ δ) * (m ν δ * x) from by intros; ring]
    simp_rw [← Finset.sum_mul]
    simp_rw [show ∀ (δ : Fin (n + 1)),
      (∑ γ : Fin (n + 1), m μ γ * met γ δ) = if μ = δ then 1 else 0 from
      fun δ => hmetric_contract μ δ]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hpot_split : 1 / 2 * ∑ μ : Fin (n + 1), m ν μ *
    (∑ α, ∑ β, m α β * (dpd α μ * pd β + pd α * dpd β μ)) =
    1 / 2 * ∑ μ, ∑ α, ∑ β, m μ ν * m α β * dpd α μ * pd β +
    1 / 2 * ∑ μ, ∑ α, ∑ β, m μ ν * m α β * pd α * dpd β μ := by
    have hsymm : ∀ (a b : Fin (n + 1)), m a b = m b a := by
      intro a b; simp only [m_def, minkowskiInverse_symm]
    rw [← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro μ _
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    simp_rw [show ∀ (α β : Fin (n + 1)),
      m ν μ * (m α β * (dpd α μ * pd β + pd α * dpd β μ)) =
      m μ ν * m α β * dpd α μ * pd β + m μ ν * m α β * pd α * dpd β μ from
      by intro α β; rw [hsymm ν μ]; ring]
    simp only [Finset.sum_add_distrib]
  rw [hkin1, hkin2, hpot_simp, hpot_split]
  ring

end CM14

namespace CM14

/--
[EMT_remainder_eq_three_terms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma EMT_remainder_eq_three_terms
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {ν : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  EMT_remainder φ p ν = (∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ α * minkowskiInverse n ν β * partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) + (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ ν * minkowskiInverse n α β * partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) + (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ ν * minkowskiInverse n α β * partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
-- proof
  unfold EMT_remainder
  have h := divEMT_explicit_expansion φ hφ p ν
  linarith

end CM14

namespace CM14

/--
[divEMT_product_rule_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma divEMT_product_rule_expansion
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {ν : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  divEnergyMomentumTensor φ p ν = waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) + (∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ α * minkowskiInverse n ν β * partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) + (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ ν * minkowskiInverse n α β * partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) + (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ ν * minkowskiInverse n α β * partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
-- proof
  have h_rem := EMT_remainder_eq_three_terms φ hφ p ν
  unfold EMT_remainder at h_rem
  linarith

end CM14

namespace CM14

/--
[three_term_schwarz_cancellation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma three_term_schwarz_cancellation
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {ν : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  (∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ α * minkowskiInverse n ν β * partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) + (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ ν * minkowskiInverse n α β * partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) + (-(1/2) * ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), minkowskiInverse n μ ν * minkowskiInverse n α β * partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) = 0 := by
-- proof
  have hA : (∑ μ : Fin (n+1), ∑ α, ∑ β, minkowskiInverse n μ α * minkowskiInverse n ν β *
    partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) =
      (∑ μ, ∑ α, ∑ β, minkowskiInverse n μ ν * minkowskiInverse n α β *
    partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
    rw [triple_sum_swap_13 (fun μ α β => minkowskiInverse n μ α * minkowskiInverse n ν β *
      partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p)]
    congr 1; ext μ; congr 1; ext α; congr 1; ext β
    rw [partialDeriv_schwarz φ hφ β μ p, minkowskiInverse_symm n β α, minkowskiInverse_symm n ν μ]
    ring
  have hB : (∑ μ : Fin (n+1), ∑ α, ∑ β, minkowskiInverse n μ ν * minkowskiInverse n α β *
    partialDeriv (fun q => partialDeriv φ α q) μ p * partialDeriv φ β p) =
      (∑ μ, ∑ α, ∑ β, minkowskiInverse n μ ν * minkowskiInverse n α β *
    partialDeriv φ α p * partialDeriv (fun q => partialDeriv φ β q) μ p) := by
    congr 1; ext μ
    conv_lhs => arg 2; ext α; arg 2; ext β; rw [partialDeriv_schwarz φ hφ μ α p]
    rw [Finset.sum_comm]
    congr 1; ext α; congr 1; ext β
    rw [minkowskiInverse_symm n β α, partialDeriv_schwarz φ hφ β μ p]
    ring
  linarith

end CM14

namespace CM14

/--
[EMT_schwarz_cancellation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma EMT_schwarz_cancellation
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {ν : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  EMT_remainder φ p ν = 0 := by
-- proof
  unfold EMT_remainder
  have h1 := divEMT_product_rule_expansion φ hφ p ν
  have h2 := three_term_schwarz_cancellation φ hφ p ν
  linarith

end CM14

namespace CM14

/--
[emt_core_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma emt_core_identity
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {ν : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  divEnergyMomentumTensor φ p ν = waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) := by
-- proof
  have h1 := EMT_product_rule_expansion φ hφ p ν
  have h2 := EMT_schwarz_cancellation φ hφ p ν
  linarith

end CM14

namespace CM14

/--
[energy_momentum_conserved](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energy_momentum_conserved
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {ν : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  divEnergyMomentumTensor φ p ν = waveOp φ p * ∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p :=
-- proof
  emt_core_identity φ hφ p ν

end CM14

namespace CM14

/--
[energy_momentum_divergence_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energy_momentum_divergence_free
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {ν : Fin (n + 1)}
-- given
  (hφ_smooth : ContDiff ℝ 2 φ)
  (hφ : ∀ p, waveOp φ p = 0) :
-- imply
  divEnergyMomentumTensor φ p ν = 0 := by
-- proof
  rw [energy_momentum_conserved φ hφ_smooth]
  simp [hφ p]

end CM14

namespace CM14

/--
[energy_momentum_divergence_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energy_momentum_divergence_lemma
  {n : ℕ}
  {φ : WaveScalarField n}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  (∀ p ν, divEnergyMomentumTensor φ p ν = waveOp φ p * ∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p) ∧ (∀ (hw : ∀ p, waveOp φ p = 0), ∀ p ν, divEnergyMomentumTensor φ p ν = 0) :=
-- proof
  ⟨fun p ν => energy_momentum_conserved φ hφ p ν,
    fun hw p ν => energy_momentum_divergence_free φ hφ hw p ν⟩

end CM14

namespace CM14

/--
[compatible_current_product_rule_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma compatible_current_product_rule_expansion
  {n : ℕ}
  {φ : WaveScalarField n}
  {X : SpacetimeVectorField n}
  {p : WaveSpacetime n} :
-- imply
  divCompatibleCurrent φ X p = divEMT_contracted_X φ X p + ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1), minkowskiInverse n α γ * minkowskiInverse n β δ * energyMomentumTensor φ p γ δ) * deformationTensor X p α β := by
-- proof
  unfold divEMT_contracted_X
  ring

end CM14

namespace CM14

/--
[symm_sum_eq_half_deformation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma symm_sum_eq_half_deformation
  [Fintype ι]
  {S : ι → ι → ℝ}
  {F : ι → ι → ℝ}
-- given
  (hS : ∀ i j, S i j = S j i) :
-- imply
  ∑ i, ∑ j, S i j * F i j = ∑ i, ∑ j, S i j * ((1/2 : ℝ) * (F i j + F j i)) := by
-- proof
  have key : ∑ i, ∑ j, S i j * F j i = ∑ i, ∑ j, S i j * F i j := by
    conv_lhs => rw [Finset.sum_comm (f := fun i j => S i j * F j i)]
    congr 1; ext j; congr 1; ext i; rw [hS j i]
  have expand : ∀ i j, S i j * (1/2 * (F i j + F j i)) =
    1/2 * (S i j * F i j) + 1/2 * (S i j * F j i) := by intros; ring
  simp_rw [expand]
  have h1 : ∑ i : ι, ∑ j : ι, (1 / 2 * (S i j * F i j) + 1 / 2 * (S i j * F j i)) =
    1/2 * (∑ i, ∑ j, S i j * F i j) + 1/2 * (∑ i, ∑ j, S i j * F j i) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1, key]; ring

end CM14

namespace CM14

/--
[energyMomentumTensor_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energyMomentumTensor_symm
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {μ ν : Fin (n + 1)} :
-- imply
  energyMomentumTensor φ p μ ν = energyMomentumTensor φ p ν μ := by
-- proof
  unfold energyMomentumTensor
  have hm : waveMinkowskiMetric n μ ν = waveMinkowskiMetric n ν μ := by
    unfold waveMinkowskiMetric; split_ifs with h1 h2 h2 <;> simp_all
  rw [hm]; ring

end CM14

namespace CM14

/--
[raised_EMT_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma raised_EMT_symm
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {α β : Fin (n + 1)} :
-- imply
  (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1), minkowskiInverse n α γ * minkowskiInverse n β δ * energyMomentumTensor φ p γ δ) = (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1), minkowskiInverse n β γ * minkowskiInverse n α δ * energyMomentumTensor φ p γ δ) := by
-- proof
  conv_lhs => arg 2; ext γ; arg 2; ext δ; rw [energyMomentumTensor_symm φ p γ δ]
  rw [Finset.sum_comm]
  congr 1; ext δ; congr 1; ext γ; ring

end CM14

namespace CM14

/--
[partialDeriv_sum_product](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma partialDeriv_sum_product
  {n : ℕ}
  {N : ℕ}
  {f g : Fin N → WaveScalarField n}
  {μ : Fin (n + 1)}
  {p : WaveSpacetime n}
-- given
  (hf : ∀ i, DifferentiableAt ℝ (f i) p)
  (hg : ∀ i, DifferentiableAt ℝ (g i) p) :
-- imply
  partialDeriv (fun q => ∑ i : Fin N, f i q * g i q) μ p = ∑ i : Fin N, (partialDeriv (f i) μ p * g i p + f i p * partialDeriv (g i) μ p) := by
-- proof
  simp only [partialDeriv]
  split_ifs with h
  ·
    have hf_s : ∀ i, DifferentiableAt ℝ (fun s => f i (s, p.2)) p.1 := fun i =>
      (hf i).comp p.1 (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const _))
    have hg_s : ∀ i, DifferentiableAt ℝ (fun s => g i (s, p.2)) p.1 := fun i =>
      (hg i).comp p.1 (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const _))
    have hfg_s : ∀ i, DifferentiableAt ℝ (fun s => f i (s, p.2) * g i (s, p.2)) p.1 :=
      fun i => (hf_s i).mul (hg_s i)
    have h_eq : (fun s => ∑ i : Fin N, f i (s, p.2) * g i (s, p.2)) =
      ∑ i : Fin N, (fun s => f i (s, p.2) * g i (s, p.2)) := by
      ext s; simp [Finset.sum_apply]
    rw [h_eq, fderiv_sum (fun i _ => hfg_s i), ContinuousLinearMap.sum_apply]
    congr 1; ext i
    have : (fun s => f i (s, p.2) * g i (s, p.2)) =
      (fun s => f i (s, p.2)) * (fun s => g i (s, p.2)) := by ext; simp [Pi.mul_apply]
    rw [this, fderiv_mul (hf_s i) (hg_s i), ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring
  ·
    have hf_s : ∀ i, DifferentiableAt ℝ (fun y => f i (p.1, y)) p.2 := fun i =>
      (hf i).comp p.2 (DifferentiableAt.prodMk (differentiableAt_const _) differentiableAt_id)
    have hg_s : ∀ i, DifferentiableAt ℝ (fun y => g i (p.1, y)) p.2 := fun i =>
      (hg i).comp p.2 (DifferentiableAt.prodMk (differentiableAt_const _) differentiableAt_id)
    have hfg_s : ∀ i, DifferentiableAt ℝ (fun y => f i (p.1, y) * g i (p.1, y)) p.2 :=
      fun i => (hf_s i).mul (hg_s i)
    have h_eq : (fun y => ∑ i : Fin N, f i (p.1, y) * g i (p.1, y)) =
      ∑ i : Fin N, (fun y => f i (p.1, y) * g i (p.1, y)) := by
      ext s; simp [Finset.sum_apply]
    rw [h_eq, fderiv_sum (fun i _ => hfg_s i), ContinuousLinearMap.sum_apply]
    congr 1; ext i
    have : (fun y => f i (p.1, y) * g i (p.1, y)) =
      (fun y => f i (p.1, y)) * (fun y => g i (p.1, y)) := by ext; simp [Pi.mul_apply]
    rw [this, fderiv_mul (hf_s i) (hg_s i), ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring

end CM14

namespace CM14

/--
[partialDeriv_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma partialDeriv_differentiable
  {n : ℕ}
  {φ : WaveScalarField n}
  {ν : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  Differentiable ℝ (fun q => partialDeriv φ ν q) := by
-- proof
  have hDiff : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hDiff_fderiv : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (by norm_num)).differentiable one_ne_zero
  have heq : (fun q => partialDeriv φ ν q) = (fun q => fderiv ℝ φ q (basisDir ν)) := by
    ext q; exact partialDeriv_eq_fderiv φ (hDiff q) ν
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ ℝ (basisDir ν)).differentiable.comp hDiff_fderiv

end CM14

namespace CM14

/--
[emt_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma emt_differentiableAt
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {γ δ : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  DifferentiableAt ℝ (fun q => energyMomentumTensor φ q γ δ) p := by
-- proof
  simp only [energyMomentumTensor]
  have hpd : ∀ ν, DifferentiableAt ℝ (fun q => partialDeriv φ ν q) p :=
    fun ν => (partialDeriv_differentiable φ hφ ν) p
  apply DifferentiableAt.sub
  · exact (hpd γ).mul (hpd δ)
  · show DifferentiableAt ℝ (fun q => (1/2 : ℝ) * waveMinkowskiMetric n γ δ *
    ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
      minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) p
    apply DifferentiableAt.mul (differentiableAt_const _)
    have h1 : (fun q => ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
      minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) =
      ∑ a : Fin (n + 1), (fun q => ∑ b : Fin (n + 1),
        minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) := by
      ext q; simp [Finset.sum_apply]
    rw [h1]
    apply DifferentiableAt.sum
    intro a _
    have h2 : (fun q => ∑ b : Fin (n + 1),
      minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) =
      ∑ b : Fin (n + 1), (fun q =>
        minkowskiInverse n a b * partialDeriv φ a q * partialDeriv φ b q) := by
      ext q; simp [Finset.sum_apply]
    rw [h2]
    apply DifferentiableAt.sum
    intro b _
    exact ((differentiableAt_const _).mul (hpd a)).mul (hpd b)

end CM14

namespace CM14

/--
[raised_EMT_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma raised_EMT_differentiableAt
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n}
  {μ α : Fin (n + 1)}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  DifferentiableAt ℝ (fun q => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1), minkowskiInverse n μ γ * minkowskiInverse n α δ * energyMomentumTensor φ q γ δ) p := by
-- proof
  have h1 : (fun q => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
    minkowskiInverse n μ γ * minkowskiInverse n α δ *
      energyMomentumTensor φ q γ δ) =
    ∑ γ : Fin (n + 1), (fun q => ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ q γ δ) := by
    ext q; simp [Finset.sum_apply]
  rw [h1]
  apply DifferentiableAt.sum
  intro γ _
  have h2 : (fun q => ∑ δ : Fin (n + 1),
    minkowskiInverse n μ γ * minkowskiInverse n α δ *
      energyMomentumTensor φ q γ δ) =
    ∑ δ : Fin (n + 1), (fun q =>
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ q γ δ) := by
    ext q; simp [Finset.sum_apply]
  rw [h2]
  apply DifferentiableAt.sum
  intro δ _
  exact (differentiableAt_const _).mul (emt_differentiableAt φ hφ p γ δ)

end CM14

namespace CM14

/--
[lowerIndex_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma lowerIndex_differentiableAt
  {n : ℕ}
  {X : SpacetimeVectorField n}
  {p : WaveSpacetime n}
  {α : Fin (n + 1)}
-- given
  (hX : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
-- imply
  DifferentiableAt ℝ (fun q => lowerIndex X q α) p := by
-- proof
  unfold lowerIndex
  have : (fun q => ∑ β : Fin (n + 1), waveMinkowskiMetric n α β * X q β) =
    (∑ β : Fin (n + 1), fun q => waveMinkowskiMetric n α β * X q β) := by
    ext q; simp [Finset.sum_apply]
  rw [this]
  exact DifferentiableAt.sum (fun β _ => (hX β).const_mul _)

end CM14

namespace CM14

/--
[divCC_product_rule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma divCC_product_rule
  {n : ℕ}
  {φ : WaveScalarField n}
  {X : SpacetimeVectorField n}
  {p : WaveSpacetime n}
-- given
  (hφ_smooth : ContDiff ℝ 2 φ)
  (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
-- imply
  divCompatibleCurrent φ X p = ∑ α : Fin (n + 1), divEnergyMomentumTensor φ p α * lowerIndex X p α + ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1), (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1), minkowskiInverse n μ γ * minkowskiInverse n α δ * energyMomentumTensor φ p γ δ) * partialDeriv (fun q => lowerIndex X q α) μ p := by
-- proof
  simp only [divCompatibleCurrent, compatibleCurrent, divEnergyMomentumTensor]
  have h_rw : ∀ μ : Fin (n + 1),
    partialDeriv (fun q =>
      ∑ α : Fin (n + 1),
        (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
          minkowskiInverse n μ γ * minkowskiInverse n α δ *
            energyMomentumTensor φ q γ δ) *
        lowerIndex X q α) μ p =
    ∑ α : Fin (n + 1),
      (partialDeriv (fun q => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n μ γ * minkowskiInverse n α δ *
          energyMomentumTensor φ q γ δ) μ p *
        lowerIndex X p α +
      (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n μ γ * minkowskiInverse n α δ *
          energyMomentumTensor φ p γ δ) *
        partialDeriv (fun q => lowerIndex X q α) μ p) := by
    intro μ
    exact partialDeriv_sum_product
      (fun α => fun q => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n μ γ * minkowskiInverse n α δ *
          energyMomentumTensor φ q γ δ)
      (fun α => fun q => lowerIndex X q α) μ p
      (fun α => raised_EMT_differentiableAt φ hφ_smooth p μ α)
      (fun α => lowerIndex_differentiableAt X p α hX_diff)
  simp_rw [h_rw, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  congr 1; ext α; rw [Finset.sum_mul]

end CM14

namespace CM14

/--
[divEMT_contracted_X_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma divEMT_contracted_X_eq
  {n : ℕ}
  {φ : WaveScalarField n}
  {X : SpacetimeVectorField n}
  {p : WaveSpacetime n}
-- given
  (hφ_smooth : ContDiff ℝ 2 φ)
  (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
-- imply
  divEMT_contracted_X φ X p = ∑ α : Fin (n + 1), divEnergyMomentumTensor φ p α * lowerIndex X p α := by
-- proof
  unfold divEMT_contracted_X
  rw [divCC_product_rule φ X hφ_smooth p hX_diff]
  suffices h : ∑ μ : Fin (n + 1), ∑ α : Fin (n + 1),
    (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ p γ δ) *
    partialDeriv (fun q => lowerIndex X q α) μ p =
    ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
      (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n α γ * minkowskiInverse n β δ *
          energyMomentumTensor φ p γ δ) *
      deformationTensor X p α β by
    linarith
  unfold deformationTensor
  exact symm_sum_eq_half_deformation
    (fun μ α => ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ *
        energyMomentumTensor φ p γ δ)
    (fun μ α => partialDeriv (fun q => lowerIndex X q α) μ p)
    (fun μ α => raised_EMT_symm φ p μ α)

end CM14

namespace CM14

/--
[divEMT_contracted_X_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma divEMT_contracted_X_vanishes
  {n : ℕ}
  {φ : WaveScalarField n}
  {X : SpacetimeVectorField n}
  {p : WaveSpacetime n}
-- given
  (hφ_smooth : ContDiff ℝ 2 φ)
  (hφ : ∀ p, waveOp φ p = 0)
  (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
-- imply
  divEMT_contracted_X φ X p = 0 := by
-- proof
  rw [divEMT_contracted_X_eq φ X hφ_smooth p hX_diff]
  simp [energy_momentum_divergence_free φ hφ_smooth hφ]

end CM14

namespace CM14

/--
[compatible_current_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma compatible_current_divergence
  {n : ℕ}
  {φ : WaveScalarField n}
  {X : SpacetimeVectorField n}
  {p : WaveSpacetime n}
-- given
  (hφ_smooth : ContDiff ℝ 2 φ)
  (hφ : ∀ p, waveOp φ p = 0)
  (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
-- imply
  divCompatibleCurrent φ X p = ∑ α : Fin (n + 1), ∑ β : Fin (n + 1), (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1), minkowskiInverse n α γ * minkowskiInverse n β δ * energyMomentumTensor φ p γ δ) * deformationTensor X p α β := by
-- proof
  have h1 := compatible_current_product_rule_expansion φ X p
  have h2 := divEMT_contracted_X_vanishes φ X hφ_smooth hφ p hX_diff
  linarith

end CM14

namespace CM14

/--
[compatible_current_divergence_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma compatible_current_divergence_free
  {n : ℕ}
  {φ : WaveScalarField n}
  {X : SpacetimeVectorField n}
  {p : WaveSpacetime n}
-- given
  (hφ_smooth : ContDiff ℝ 2 φ)
  (hφ : ∀ p, waveOp φ p = 0)
  (hX : ∀ p μ ν, deformationTensor X p μ ν = 0)
  (hX_diff : ∀ β, DifferentiableAt ℝ (fun q => X q β) p) :
-- imply
  divCompatibleCurrent φ X p = 0 := by
-- proof
  rw [compatible_current_divergence φ X hφ_smooth hφ p hX_diff]
  simp [hX]

end CM14

namespace CM14

/--
[waveEuclidNormSq_component_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma waveEuclidNormSq_component_le
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n} :
-- imply
  x i ^ 2 ≤ waveEuclidNormSq x :=
-- proof
  Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

end CM14

namespace CM14

/--
[norm_le_of_waveEuclidNormSq_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma norm_le_of_waveEuclidNormSq_le
  {n : ℕ}
  {x : Fin n → ℝ}
  {R : ℝ}
-- given
  (hR : 0 ≤ R)
  (h : waveEuclidNormSq x ≤ R ^ 2) :
-- imply
  ‖x‖ ≤ R := by
-- proof
  rw [pi_norm_le_iff_of_nonneg hR]
  intro i
  rw [Real.norm_eq_abs]
  apply abs_le_of_sq_le_sq _ hR
  calc (x i) ^ 2 ≤ waveEuclidNormSq x := waveEuclidNormSq_component_le x i
    _ ≤ R ^ 2 := h

end CM14

namespace CM14

/--
[truncatedBackwardsCone_isBounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma truncatedBackwardsCone_isBounded
  {n : ℕ}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
  {t : ℝ}
-- given
  (hR : 0 < R)
  (_ht : 0 ≤ t)
  (htR : t ≤ R) :
-- imply
  Bornology.IsBounded (truncatedBackwardsCone x₀ R 0 t) := by
-- proof
  apply Metric.isBounded_closedBall (x := (0, x₀)) (r := R) |>.subset
  intro ⟨τ, y⟩ hp
  simp only [truncatedBackwardsCone, mem_setOf_eq] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [Metric.mem_closedBall, Prod.dist_eq]
  apply max_le
  · rw [Real.dist_eq, sub_zero, abs_of_nonneg h1]; linarith
  · rw [dist_eq_norm]
    apply norm_le_of_waveEuclidNormSq_le _ R hR.le
    calc waveEuclidNormSq (y - x₀) ≤ (R - τ) ^ 2 := h3
      _ ≤ R ^ 2 := by nlinarith

end CM14

namespace CM14

/--
[truncatedBackwardsCone_isRegularDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma truncatedBackwardsCone_isRegularDomain
  {n : ℕ}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
  {t : ℝ}
-- given
  (hR : 0 < R)
  (ht : 0 ≤ t)
  (htR : t ≤ R) :
-- imply
  IsRegularDomain (interior (truncatedBackwardsCone x₀ R 0 t)) := by
-- proof
  have hbdd : Bornology.IsBounded (interior (truncatedBackwardsCone x₀ R 0 t)) :=
    (truncatedBackwardsCone_isBounded x₀ R hR t ht htR).subset interior_subset
  exact ⟨isOpen_interior, hbdd, hbdd.isCompact_closure⟩

end CM14

namespace CM14

/--
[partialDeriv_lowerIndex_killing_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma partialDeriv_lowerIndex_killing_eq_zero
  {n : ℕ}
  {ν μ : Fin (n + 1)}
  {p : WaveSpacetime n} :
-- imply
  partialDeriv (fun q => lowerIndex (pastTimelikeKillingField n) q ν) μ p = 0 := by
-- proof
  unfold partialDeriv
  split
  ·
    have : (fun s => lowerIndex (pastTimelikeKillingField n) (s, p.2) ν) =
      fun _ => lowerIndex (pastTimelikeKillingField n) (0, p.2) ν := by
      ext s; simp [lowerIndex, pastTimelikeKillingField]
    rw [this]; simp
  ·
    have : (fun y => lowerIndex (pastTimelikeKillingField n) (p.1, y) ν) =
      fun _ => lowerIndex (pastTimelikeKillingField n) (p.1, 0) ν := by
      ext y; simp [lowerIndex, pastTimelikeKillingField]
    rw [this]; simp

end CM14

namespace CM14

/--
[pastTimelikeKillingField_isKilling](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma pastTimelikeKillingField_isKilling
  {n : ℕ}
  {p : WaveSpacetime n}
  {μ ν : Fin (n + 1)} :
-- imply
  deformationTensor (pastTimelikeKillingField n) p μ ν = 0 := by
-- proof
  unfold deformationTensor
  rw [partialDeriv_lowerIndex_killing_eq_zero,
    partialDeriv_lowerIndex_killing_eq_zero]
  ring

end CM14

namespace CM14

/--
[mantleFace_flux_eq_mantleFlux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma mantleFace_flux_eq_mantleFlux
  {n : ℕ}
  {φ : WaveScalarField n}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
  {t : ℝ}
-- given
  (_hφ_smooth : ContDiff ℝ 2 φ)
  (_hR : 0 < R)
  (_ht : 0 ≤ t)
  (_htR : t ≤ R) :
-- imply
  let Ω := interior (truncatedBackwardsCone x₀ R 0 t) let X := pastTimelikeKillingField n let M := coneMantle x₀ R t ∫ σ in M, (∑ α : Fin (n + 1), outwardUnitNormal Ω σ α * compatibleCurrent φ X σ α) ∂(Measure.hausdorffMeasure n) = mantleFlux φ x₀ R t := by
-- proof
  simp only [mantleFlux]

end CM14

namespace CM14

/--
[waveMinkowskiMetric_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma waveMinkowskiMetric_symm
  {n : ℕ}
  {μ ν : Fin (n + 1)} :
-- imply
  waveMinkowskiMetric n μ ν = waveMinkowskiMetric n ν μ := by
-- proof
  simp only [waveMinkowskiMetric]; split_ifs <;> simp_all [eq_comm]

end CM14

namespace CM14

/--
[waveMinkowskiMetric_sq_diag](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma waveMinkowskiMetric_sq_diag
  {n : ℕ}
  {k : Fin (n + 1)} :
-- imply
  waveMinkowskiMetric n k k * waveMinkowskiMetric n k k = 1 := by
-- proof
  simp only [waveMinkowskiMetric, ite_true]; split_ifs <;> ring

end CM14

namespace CM14

/--
[waveMinkowskiMetric_row_select](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma waveMinkowskiMetric_row_select
  {n : ℕ}
  {k : Fin (n + 1)}
  {f : Fin (n + 1) → ℝ} :
-- imply
  ∑ β : Fin (n + 1), waveMinkowskiMetric n k β * f β = waveMinkowskiMetric n k k * f k := by
-- proof
  simp_rw [waveMinkowskiMetric_symm n k]
  rw [show ∑ β, waveMinkowskiMetric n β k * f β =
    ∑ β ∈ Finset.univ, waveMinkowskiMetric n β k * f β from rfl]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
  intro b _ hb; simp [waveMinkowskiMetric, hb]

end CM14

namespace CM14

/--
[mantleFlux_integrand_eq_DEC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma mantleFlux_integrand_eq_DEC
  {n : ℕ}
  {φ : WaveScalarField n}
  {x₀ : Fin n → ℝ}
  {R t : ℝ}
  {σ : WaveSpacetime n} :
-- imply
  let Ω := interior (truncatedBackwardsCone x₀ R 0 t) let N := outwardUnitNormal Ω σ let X := pastTimelikeKillingField n ∑ α : Fin (n + 1), N α * compatibleCurrent φ X σ α = ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1), energyMomentumTensor φ σ γ δ * raiseIndex N γ * (X σ δ) := by
-- proof
  intro Ω N X
  simp only [compatibleCurrent, lowerIndex, raiseIndex, minkowskiInverse]
  simp_rw [waveMinkowskiMetric_row_select n _ (X σ)]
  have h2 : ∀ (α a γ : Fin (n + 1)),
    ∑ δ : Fin (n + 1), waveMinkowskiMetric n α γ * waveMinkowskiMetric n a δ *
      energyMomentumTensor φ σ γ δ =
    waveMinkowskiMetric n α γ *
      (waveMinkowskiMetric n a a * energyMomentumTensor φ σ γ a) := by
    intro α a γ
    conv_lhs =>
      arg 2; ext δ
      rw [show waveMinkowskiMetric n α γ * waveMinkowskiMetric n a δ *
        energyMomentumTensor φ σ γ δ =
        waveMinkowskiMetric n α γ *
          (waveMinkowskiMetric n a δ * energyMomentumTensor φ σ γ δ) by ring]
    rw [← Finset.mul_sum]
    congr 1
    exact waveMinkowskiMetric_row_select n a (energyMomentumTensor φ σ γ)
  simp_rw [h2]
  have h3 : ∀ (α a : Fin (n + 1)),
    (∑ γ, waveMinkowskiMetric n α γ *
      (waveMinkowskiMetric n a a * energyMomentumTensor φ σ γ a)) *
      (waveMinkowskiMetric n a a * X σ a) =
    (∑ γ, waveMinkowskiMetric n α γ * energyMomentumTensor φ σ γ a) * X σ a := by
    intro α a
    conv_lhs =>
      arg 1; arg 2; ext γ
      rw [show waveMinkowskiMetric n α γ *
        (waveMinkowskiMetric n a a * energyMomentumTensor φ σ γ a) =
        waveMinkowskiMetric n a a *
          (waveMinkowskiMetric n α γ * energyMomentumTensor φ σ γ a) by ring]
    rw [← Finset.mul_sum,
      show waveMinkowskiMetric n a a *
        (∑ γ, waveMinkowskiMetric n α γ * energyMomentumTensor φ σ γ a) *
        (waveMinkowskiMetric n a a * X σ a) =
        (waveMinkowskiMetric n a a * waveMinkowskiMetric n a a) *
          (∑ γ, waveMinkowskiMetric n α γ * energyMomentumTensor φ σ γ a) *
          X σ a by ring,
      waveMinkowskiMetric_sq_diag, one_mul]
  simp_rw [h3]
  simp_rw [waveMinkowskiMetric_row_select n _ (fun γ => energyMomentumTensor φ σ γ _)]
  simp_rw [waveMinkowskiMetric_row_select n _ N]
  congr 1; ext x
  rw [Finset.mul_sum]
  congr 1; ext i
  ring

end CM14

namespace CM14

/--
[waveMinkowskiMetric_off_diag](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma waveMinkowskiMetric_off_diag
  {n : ℕ}
  {α β : Fin (n + 1)}
-- given
  (h : α ≠ β) :
-- imply
  waveMinkowskiMetric n α β = 0 := by
-- proof
  simp [waveMinkowskiMetric, h]

end CM14

namespace CM14

/--
[raiseIndex_eq_diag](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma raiseIndex_eq_diag
  {n : ℕ}
  {N : Fin (n + 1) → ℝ}
  {γ : Fin (n + 1)} :
-- imply
  raiseIndex N γ = waveMinkowskiMetric n γ γ * N γ := by
-- proof
  unfold raiseIndex minkowskiInverse
  conv_lhs =>
    arg 2; ext μ
    rw [show waveMinkowskiMetric n γ μ * N μ =
      if γ = μ then waveMinkowskiMetric n γ γ * N γ else 0 from by
      split_ifs with h
      · subst h; ring
      · simp [waveMinkowskiMetric_off_diag γ μ h]]
  simp

end CM14

namespace CM14

/--
[minkowskiProduct_raiseIndex_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma minkowskiProduct_raiseIndex_self
  {n : ℕ}
  {N : Fin (n + 1) → ℝ} :
-- imply
  minkowskiProduct (raiseIndex N) (raiseIndex N) = minkowskiProduct N N := by
-- proof
  simp only [minkowskiProduct, raiseIndex_eq_diag]
  congr 1; ext α
  congr 1; ext β
  by_cases hab : α = β
  · subst hab
    simp only [waveMinkowskiMetric]
    split_ifs <;> ring
  · simp [waveMinkowskiMetric_off_diag α β hab]

end CM14

namespace CM14

/--
[pastTimelikeKillingField_isPastCausal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma pastTimelikeKillingField_isPastCausal
  {n : ℕ}
  {σ : WaveSpacetime n} :
-- imply
  IsPastCausal (pastTimelikeKillingField n σ) := by
-- proof
  constructor
  ·
    unfold IsPastDirected pastTimelikeKillingField
    simp
  ·
    unfold minkowskiProduct waveMinkowskiMetric pastTimelikeKillingField
    simp

end CM14

namespace CM14

/--
[diff_outer_t'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma diff_outer_t'
  {n : ℕ}
  {φ : WaveScalarField n}
  {x₀ : Fin n → ℝ}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  Differentiable ℝ (fun s => (fderiv ℝ (fun r => φ (r, x₀)) s) 1) := by
-- proof
  have h : ContDiff ℝ 2 (fun r : ℝ => φ (r, x₀)) := hφ.comp₂ contDiff_id contDiff_const
  have heq : (fun s => (fderiv ℝ (fun r => φ (r, x₀)) s) 1) = deriv (fun r => φ (r, x₀)) := by ext s; simp
  rw [heq]; have h2 : ContDiff ℝ (1 + 1) (fun r : ℝ => φ (r, x₀)) := by convert h using 2
  exact h2.deriv'.differentiable (by decide)

end CM14

namespace CM14

/--
[diff_outer_x'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma diff_outer_x'
  {n : ℕ}
  {φ : WaveScalarField n}
  {t₀ : ℝ}
  {i : Fin n}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  Differentiable ℝ (fun y => (fderiv ℝ (fun z => φ (t₀, z)) y) (Pi.single i 1)) := by
-- proof
  have h_fderiv_smooth : ContDiff ℝ 1 (fun y : Fin n → ℝ => fderiv ℝ (fun z => φ (t₀, z)) y) :=
    ContDiff.fderiv (hφ.comp₂ contDiff_const contDiff_snd) contDiff_id (by decide)
  exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).contDiff.fun_comp h_fderiv_smooth).differentiable (by decide)

end CM14

namespace CM14

/--
[waveOp_linearity_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma waveOp_linearity_sub
  {n : ℕ}
  {φ₁ φ₂ : WaveScalarField n}
  {p : WaveSpacetime n}
-- given
  (hφ₁ : ContDiff ℝ 2 φ₁)
  (hφ₂ : ContDiff ℝ 2 φ₂) :
-- imply
  waveOp (fun q => φ₁ q - φ₂ q) p = waveOp φ₁ p - waveOp φ₂ p := by
-- proof
  unfold waveOp
  have hd1t : ∀ s, DifferentiableAt ℝ (fun r => φ₁ (r, p.2)) s :=
    fun s => ((hφ₁.comp₂ contDiff_id contDiff_const).differentiable (by decide)).differentiableAt
  have hd2t : ∀ s, DifferentiableAt ℝ (fun r => φ₂ (r, p.2)) s :=
    fun s => ((hφ₂.comp₂ contDiff_id contDiff_const).differentiable (by decide)).differentiableAt
  have hd1x : ∀ y, DifferentiableAt ℝ (fun z => φ₁ (p.1, z)) y :=
    fun y => ((hφ₁.comp₂ contDiff_const contDiff_id).differentiable (by decide)).differentiableAt
  have hd2x : ∀ y, DifferentiableAt ℝ (fun z => φ₂ (p.1, z)) y :=
    fun y => ((hφ₂.comp₂ contDiff_const contDiff_id).differentiable (by decide)).differentiableAt
  have htime_fn : (fun s => fderiv ℝ (fun r => φ₁ (r, p.2) - φ₂ (r, p.2)) s 1) =
    (fun s => fderiv ℝ (fun r => φ₁ (r, p.2)) s 1 - fderiv ℝ (fun r => φ₂ (r, p.2)) s 1) := by
    ext s
    show (fderiv ℝ ((fun r => φ₁ (r, p.2)) - fun r => φ₂ (r, p.2)) s) 1 = _
    rw [fderiv_sub (hd1t s) (hd2t s), ContinuousLinearMap.sub_apply]
  have hspace_fn : ∀ i : Fin n, (fun y => fderiv ℝ (fun z => φ₁ (p.1, z) - φ₂ (p.1, z)) y (Pi.single i 1)) =
    (fun y => fderiv ℝ (fun z => φ₁ (p.1, z)) y (Pi.single i 1) - fderiv ℝ (fun z => φ₂ (p.1, z)) y (Pi.single i 1)) := by
    intro i; ext y
    show (fderiv ℝ ((fun z => φ₁ (p.1, z)) - fun z => φ₂ (p.1, z)) y) (Pi.single i 1) = _
    rw [fderiv_sub (hd1x y) (hd2x y), ContinuousLinearMap.sub_apply]
  rw [htime_fn]; simp_rw [hspace_fn]
  have houter_t :
    (fderiv ℝ (fun s => (fderiv ℝ (fun r => φ₁ (r, p.2)) s) 1 - (fderiv ℝ (fun r => φ₂ (r, p.2)) s) 1) p.1) 1 =
    (fderiv ℝ (fun s => (fderiv ℝ (fun r => φ₁ (r, p.2)) s) 1) p.1) 1 - (fderiv ℝ (fun s => (fderiv ℝ (fun r => φ₂ (r, p.2)) s) 1) p.1) 1 := by
    rw [show (fun s => (fderiv ℝ (fun r => φ₁ (r, p.2)) s) 1 - (fderiv ℝ (fun r => φ₂ (r, p.2)) s) 1) =
      ((fun s => (fderiv ℝ (fun r => φ₁ (r, p.2)) s) 1) - (fun s => (fderiv ℝ (fun r => φ₂ (r, p.2)) s) 1)) from rfl]
    rw [fderiv_sub (diff_outer_t' φ₁ hφ₁ p.2).differentiableAt (diff_outer_t' φ₂ hφ₂ p.2).differentiableAt,
      ContinuousLinearMap.sub_apply]
  have houter_x : ∀ i : Fin n,
    (fderiv ℝ (fun y => (fderiv ℝ (fun z => φ₁ (p.1, z)) y) (Pi.single i 1) - (fderiv ℝ (fun z => φ₂ (p.1, z)) y) (Pi.single i 1)) p.2) (Pi.single i 1) =
    (fderiv ℝ (fun y => (fderiv ℝ (fun z => φ₁ (p.1, z)) y) (Pi.single i 1)) p.2) (Pi.single i 1) -
    (fderiv ℝ (fun y => (fderiv ℝ (fun z => φ₂ (p.1, z)) y) (Pi.single i 1)) p.2) (Pi.single i 1) := by
    intro i
    rw [show (fun y => (fderiv ℝ (fun z => φ₁ (p.1, z)) y) (Pi.single i 1) - (fderiv ℝ (fun z => φ₂ (p.1, z)) y) (Pi.single i 1)) =
      ((fun y => (fderiv ℝ (fun z => φ₁ (p.1, z)) y) (Pi.single i 1)) - (fun y => (fderiv ℝ (fun z => φ₂ (p.1, z)) y) (Pi.single i 1))) from rfl]
    rw [fderiv_sub (diff_outer_x' φ₁ hφ₁ p.1 i).differentiableAt (diff_outer_x' φ₂ hφ₂ p.1 i).differentiableAt,
      ContinuousLinearMap.sub_apply]
  rw [houter_t]; simp_rw [houter_x, Finset.sum_sub_distrib]
  ring

end CM14

namespace CM14

/--
[fderiv_sub_energy_density](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma fderiv_sub_energy_density
  {n : ℕ}
  {φ₁ φ₂ : WaveScalarField n}
  {x : Fin n → ℝ}
-- given
  (hφ₁ : ContDiff ℝ 2 φ₁)
  (hφ₂ : ContDiff ℝ 2 φ₂) :
-- imply
  energyDensity (fun q => φ₁ q - φ₂ q) (0, x) = (1/2 : ℝ) * ((fderiv ℝ (fun s => φ₁ (s, x)) 0 1 - fderiv ℝ (fun s => φ₂ (s, x)) 0 1) ^ 2 + ∑ i : Fin n, (fderiv ℝ (fun y => φ₁ (0, y)) x (Pi.single i 1) - fderiv ℝ (fun y => φ₂ (0, y)) x (Pi.single i 1)) ^ 2) := by
-- proof
  unfold energyDensity
  simp only []
  congr 1; congr 1
  · congr 1
    have hd1 : DifferentiableAt ℝ (fun s => φ₁ (s, x)) 0 :=
      ((hφ₁.comp₂ contDiff_id contDiff_const).differentiable (by decide)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun s => φ₂ (s, x)) 0 :=
      ((hφ₂.comp₂ contDiff_id contDiff_const).differentiable (by decide)).differentiableAt
    show (fderiv ℝ ((fun s => φ₁ (s, x)) - fun s => φ₂ (s, x)) 0) 1 = _
    rw [fderiv_sub hd1 hd2, ContinuousLinearMap.sub_apply]
  · congr 1; ext i; congr 1
    have hd1 : DifferentiableAt ℝ (fun y => φ₁ (0, y)) x :=
      ((hφ₁.comp₂ contDiff_const contDiff_id).differentiable (by decide)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun y => φ₂ (0, y)) x :=
      ((hφ₂.comp₂ contDiff_const contDiff_id).differentiable (by decide)).differentiableAt
    show (fderiv ℝ ((fun y => φ₁ (0, y)) - fun y => φ₂ (0, y)) x) (Pi.single i 1) = _
    rw [fderiv_sub hd1 hd2, ContinuousLinearMap.sub_apply]

end CM14

namespace CM14

/--
[same_data_spatial_deriv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma same_data_spatial_deriv_eq
  {n : ℕ}
  {φ₁ φ₂ : WaveScalarField n}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
  {x : Fin n → ℝ}
  {i : Fin n}
-- given
  (hφ₁ : ContDiff ℝ 2 φ₁)
  (hφ₂ : ContDiff ℝ 2 φ₂)
  (hR : 0 < R)
  (h_data : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ₁ (0, x) = φ₂ (0, x))
  (hx : waveEuclidNormSq (x - x₀) ≤ R ^ 2) :
-- imply
  fderiv ℝ (fun y => φ₁ (0, y)) x (Pi.single i 1) = fderiv ℝ (fun y => φ₂ (0, y)) x (Pi.single i 1) := by
-- proof
  let g : (Fin n → ℝ) → ℝ := fun y => φ₁ (0, y) - φ₂ (0, y)
  suffices h : fderiv ℝ g x (Pi.single i 1) = 0 by
    have hd1 : DifferentiableAt ℝ (fun y => φ₁ (0, y)) x :=
      ((hφ₁.comp (contDiff_prodMk_right (0 : ℝ))).differentiable (by decide)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun y => φ₂ (0, y)) x :=
      ((hφ₂.comp (contDiff_prodMk_right (0 : ℝ))).differentiable (by decide)).differentiableAt
    rw [show fderiv ℝ g x = fderiv ℝ (fun y => φ₁ (0, y)) x - fderiv ℝ (fun y => φ₂ (0, y)) x
      from fderiv_sub hd1 hd2, ContinuousLinearMap.sub_apply] at h; linarith
  have hg : ContDiff ℝ 2 g :=
    (hφ₁.comp (contDiff_prodMk_right (0 : ℝ))).sub (hφ₂.comp (contDiff_prodMk_right (0 : ℝ)))
  have hg_zero : ∀ y, waveEuclidNormSq (y - x₀) ≤ R ^ 2 → g y = 0 :=
    fun y hy => sub_eq_zero.mpr (h_data y hy)
  have hS_open : IsOpen {y : Fin n → ℝ | waveEuclidNormSq (y - x₀) < R ^ 2} :=
    isOpen_lt (continuous_finset_sum _ fun j _ => ((continuous_apply j).sub continuous_const).pow 2)
      continuous_const
  have hF_cont : Continuous (fun y => fderiv ℝ g y (Pi.single i 1)) := by
    show Continuous ((fun L : ((Fin n → ℝ) →L[ℝ] ℝ) => L (Pi.single i 1)) ∘ (fderiv ℝ g))
    exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).continuous).comp
      (hg.continuous_fderiv (by decide))
  have hF_zero_int : ∀ y, waveEuclidNormSq (y - x₀) < R ^ 2 →
    fderiv ℝ g y (Pi.single i 1) = 0 := by
    intro y hy
    have h_eq : g =ᶠ[nhds y] 0 :=
      Filter.eventually_iff_exists_mem.mpr ⟨_, hS_open.mem_nhds hy, fun z hz => hg_zero z hz.le⟩
    simp [Filter.EventuallyEq.fderiv_eq h_eq]
  obtain h_int | h_bdy := lt_or_eq_of_le hx
  ·
    exact hF_zero_int x h_int
  ·
    by_cases hR2 : R ^ 2 ≤ 0
    ·
      exact absurd (not_le.mpr (sq_pos_of_pos hR)) (not_not.mpr hR2)
    ·
      simp only [not_le] at hR2
      let γ : ℝ → Fin n → ℝ := fun t j => x₀ j + (1 - t) * (x j - x₀ j)
      have hγ0 : γ 0 = x := by ext j; simp [γ]
      have hFγ_cont : ContinuousAt (fun t => fderiv ℝ g (γ t) (Pi.single i 1)) 0 :=
        hF_cont.continuousAt.comp (continuousAt_pi.mpr fun j => by
          simp only [γ]; exact continuousAt_const.add
            ((continuousAt_const.sub continuousAt_id).mul continuousAt_const))
      have hγ_int : ∀ t, 0 < t → t < 1 → waveEuclidNormSq (γ t - x₀) < R ^ 2 := by
        intro t ht0 ht1
        show ∑ j, (γ t j - x₀ j) ^ 2 < R ^ 2
        simp only [γ, add_sub_cancel_left]
        conv_lhs => arg 2; ext j; rw [mul_pow]
        rw [← Finset.mul_sum, show ∑ j : Fin n, (x j - x₀ j) ^ 2 = R ^ 2 from h_bdy]
        have h1t : (1 - t) ^ 2 < 1 := by nlinarith
        have : (1 - t) ^ 2 * R ^ 2 < 1 * R ^ 2 := by nlinarith
        linarith
      rw [← hγ0]
      by_contra h_ne
      obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hFγ_cont _ (abs_pos.mpr h_ne)
      set t₀ := min (δ / 2) (1 / 2)
      have ht₀_pos : 0 < t₀ := lt_min (half_pos hδ0) (by norm_num)
      have ht₀_lt_δ : dist t₀ 0 < δ := by
        simp [abs_of_pos ht₀_pos]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ0)
      have ht₀_lt_1 : t₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have h1 := hδ ht₀_lt_δ
      rw [hF_zero_int _ (hγ_int t₀ ht₀_pos ht₀_lt_1)] at h1
      simp at h1

end CM14

namespace CM14

/--
[same_data_zero_energy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma same_data_zero_energy
  {n : ℕ}
  {φ₁ φ₂ : WaveScalarField n}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
-- given
  (hφ₁ : ContDiff ℝ 2 φ₁)
  (hφ₂ : ContDiff ℝ 2 φ₂)
  (hR : 0 < R)
  (h_data : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ₁ (0, x) = φ₂ (0, x))
  (h_vel : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → fderiv ℝ (fun s => φ₁ (s, x)) 0 1 = fderiv ℝ (fun s => φ₂ (s, x)) 0 1) :
-- imply
  energyOnBall (fun q => φ₁ q - φ₂ q) 0 x₀ R = 0 := by
-- proof
  unfold energyOnBall
  have h_integrand_zero : (fun x : Fin n → ℝ =>
    if waveEuclidNormSq (x - x₀) ≤ R ^ 2
    then energyDensity (fun q => φ₁ q - φ₂ q) (0, x) else 0) = 0 := by
    ext x
    simp only [Pi.zero_apply]
    split_ifs with hx
    · rw [fderiv_sub_energy_density φ₁ φ₂ hφ₁ hφ₂]
      have hvel := h_vel x hx
      have hspatial : ∀ i : Fin n,
        fderiv ℝ (fun y => φ₁ (0, y)) x (Pi.single i 1) =
        fderiv ℝ (fun y => φ₂ (0, y)) x (Pi.single i 1) :=
        fun i => same_data_spatial_deriv_eq φ₁ φ₂ hφ₁ hφ₂ x₀ R hR h_data x hx i
      simp [hvel, hspatial]
    · rfl
  rw [h_integrand_zero]
  simp

end CM14

namespace CM14

/--
[energyDensity_integrable_on_ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energyDensity_integrable_on_ball
  {n : ℕ}
  {φ : WaveScalarField n}
  {t : ℝ}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
-- given
  (hφ : ContDiff ℝ 2 φ) :
-- imply
  Integrable (fun x : Fin n → ℝ => if waveEuclidNormSq (x - x₀) ≤ R ^ 2 then energyDensity φ (t, x) else 0) := by
-- proof
  set S := {x : Fin n → ℝ | waveEuclidNormSq (x - x₀) ≤ R ^ 2} with hS_def
  have hfun : (fun x : Fin n → ℝ =>
    if waveEuclidNormSq (x - x₀) ≤ R ^ 2 then energyDensity φ (t, x) else 0) =
    S.indicator (fun x => energyDensity φ (t, x)) := by
    ext x; simp only [S, Set.indicator, Set.mem_setOf_eq]
  rw [hfun]
  have hS_closed : IsClosed S := by
    have : S = (fun x => waveEuclidNormSq (x - x₀)) ⁻¹' Set.Iic (R ^ 2) := by
      ext x; simp [S, Set.mem_preimage, Set.mem_Iic]
    rw [this]
    apply IsClosed.preimage _ isClosed_Iic
    exact (continuous_finset_sum _ (fun i _ => (continuous_apply i |>.comp (continuous_id.sub continuous_const)).pow 2))
  have hS_bounded : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_ball x₀]
    refine ⟨|R| + 1, fun x hx => ?_⟩
    simp only [S, Set.mem_setOf_eq] at hx
    rw [Metric.mem_ball, dist_comm]
    have : ‖x - x₀‖ ≤ |R| := by
      rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
      intro i
      have hi : (x - x₀) i ^ 2 ≤ R ^ 2 := by
        calc (x - x₀) i ^ 2
          ≤ ∑ j, (x - x₀) j ^ 2 := single_le_sum (fun j _ => sq_nonneg ((x - x₀) j)) (mem_univ i)
          _ = waveEuclidNormSq (x - x₀) := rfl
          _ ≤ R ^ 2 := hx
      rw [Real.norm_eq_abs]
      exact abs_le_of_sq_le_sq (hi.trans (by rw [sq_abs])) (abs_nonneg R)
    calc dist x₀ x = ‖x₀ - x‖ := dist_eq_norm x₀ x
      _ = ‖-(x - x₀)‖ := by ring_nf
      _ = ‖x - x₀‖ := norm_neg _
      _ ≤ |R| := this
      _ < |R| + 1 := lt_add_one _
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have hcont : Continuous (fun x : Fin n → ℝ => energyDensity φ (t, x)) := by
    unfold energyDensity
    apply Continuous.mul continuous_const
    apply Continuous.add
    · apply Continuous.pow
      have hswap : ContDiff ℝ 2
        (Function.uncurry (fun (x : Fin n → ℝ) (s : ℝ) => φ (s, x))) := by
        show ContDiff ℝ 2 (φ ∘ Prod.swap)
        exact hφ.comp (contDiff_snd.prodMk contDiff_fst)
      exact (hswap.fderiv_apply (n := 0) contDiff_const contDiff_const
        (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 2)).continuous
    · apply continuous_finset_sum; intro i _
      apply Continuous.pow
      have h1 : ContDiff ℝ 2 (fun y : Fin n → ℝ => φ (t, y)) :=
        hφ.comp (contDiff_const.prodMk contDiff_id)
      exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).continuous.comp
        (h1.fderiv_right (m := 1) (by norm_num)).continuous)
  rw [integrable_indicator_iff hS_closed.measurableSet]
  exact ContinuousOn.integrableOn_compact hS_compact hcont.continuousOn

end CM14

namespace CM14

/--
[continuous_zero_of_ae_imp_on_interior](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma continuous_zero_of_ae_imp_on_interior
  {n : ℕ}
  {f : (Fin n → ℝ) → ℝ}
  {S : Set (Fin n → ℝ)}
  {x : Fin n → ℝ}
-- given
  (hf : Continuous f)
  (hae : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), x ∈ S → f x = 0)
  (hx : x ∈ interior S) :
-- imply
  f x = 0 := by
-- proof
  by_contra h
  have hopen : IsOpen {y : Fin n → ℝ | f y ≠ 0} := isOpen_ne_fun hf continuous_const
  have hinter_open : IsOpen ({y | f y ≠ 0} ∩ interior S) := hopen.inter isOpen_interior
  have hinter_ne : ({y | f y ≠ 0} ∩ interior S).Nonempty := ⟨x, h, hx⟩
  have hpos := hinter_open.measure_pos (μ := (volume : Measure (Fin n → ℝ))) hinter_ne
  rw [ae_iff] at hae
  have hsub : {y | f y ≠ 0} ∩ interior S ⊆ {a | ¬(a ∈ S → f a = 0)} :=
    fun y ⟨hy1, hy2⟩ => fun hc => hy1 (hc (interior_subset hy2))
  exact absurd (le_antisymm (le_trans (measure_mono hsub) hae.le) (zero_le _)) (ne_of_gt hpos)

end CM14

namespace CM14

/--
[mem_interior_of_waveEuclidNormSq_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma mem_interior_of_waveEuclidNormSq_lt
  {n : ℕ}
  {x₀ : Fin n → ℝ}
  {r : ℝ}
  {x : Fin n → ℝ}
-- given
  (hx : waveEuclidNormSq (x - x₀) < r ^ 2) :
-- imply
  x ∈ interior {y : Fin n → ℝ | waveEuclidNormSq (y - x₀) ≤ r ^ 2} := by
-- proof
  have hcont : Continuous (fun y : Fin n → ℝ => waveEuclidNormSq (y - x₀)) :=
    (continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)).comp
      (continuous_id.sub continuous_const)
  have hopen : IsOpen {y : Fin n → ℝ | waveEuclidNormSq (y - x₀) < r ^ 2} :=
    isOpen_lt hcont continuous_const
  exact interior_mono
    (fun y (hy : waveEuclidNormSq (y - x₀) < r ^ 2) => le_of_lt hy)
    (hopen.subset_interior_iff.mpr le_rfl hx)

end CM14

namespace CM14

/--
[zero_derivs_ae_imply_zero_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma zero_derivs_ae_imply_zero_field
  {n : ℕ}
  {φ : WaveScalarField n}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
  {t : ℝ}
  {x : Fin n → ℝ}
-- given
  (hφ_smooth : ContDiff ℝ 2 φ)
  (hR : 0 < R)
  (hφ_zero_init : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ (0, x) = 0)
  (hdt : ∀ t, 0 ≤ t → t ≤ R → ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 → fderiv ℝ (fun s => φ (s, x)) t 1 = 0)
  (_hdx : ∀ t, 0 ≤ t → t ≤ R → ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 → ∀ i : Fin n, fderiv ℝ (fun y => φ (t, y)) x (Pi.single i 1) = 0)
  (ht0 : 0 ≤ t)
  (htR : t ≤ R)
  (hx : waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2) :
-- imply
  φ (t, x) = 0 := by
-- proof
  set f := fun s => φ (s, x) with hf_def
  have hslice : ContDiff ℝ 2 f := hφ_smooth.comp (contDiff_id.prodMk contDiff_const)
  have hf_diff : Differentiable ℝ f := hslice.differentiable (by norm_num)
  have hf0 : f 0 = 0 := hφ_zero_init x (by nlinarith)
  have hdt_cont : ∀ s, Continuous (fun y : Fin n → ℝ => fderiv ℝ (fun s' => φ (s', y)) s 1) := by
    intro s
    have hswap : ContDiff ℝ 2 (Function.uncurry (fun (y : Fin n → ℝ) (s : ℝ) => φ (s, y))) := by
      show ContDiff ℝ 2 (φ ∘ Prod.swap)
      exact hφ_smooth.comp (contDiff_snd.prodMk contDiff_fst)
    exact (hswap.fderiv_apply (n := 0) contDiff_const contDiff_const
      (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 2)).continuous
  have hderiv_zero : ∀ s ∈ Ioo 0 t, HasDerivAt f 0 s := by
    intro s ⟨hs0, hst⟩
    have hhas : HasDerivAt f (fderiv ℝ f s 1) s := hf_diff.differentiableAt.hasDerivAt
    have hball_strict : waveEuclidNormSq (x - x₀) < (R - s) ^ 2 := by nlinarith
    have := continuous_zero_of_ae_imp_on_interior (hdt_cont s)
      (hdt s (le_of_lt hs0) (le_trans (le_of_lt hst) htR))
      (mem_interior_of_waveEuclidNormSq_lt hball_strict)
    rwa [this] at hhas
  have hftc : ∫ s in (0 : ℝ)..t, (0 : ℝ) = f t - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht0
      hf_diff.continuous.continuousOn hderiv_zero intervalIntegrable_const
  simp at hftc
  linarith

end CM14

namespace CM14

/--
[energyDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energyDensity_nonneg
  {n : ℕ}
  {φ : WaveScalarField n}
  {p : WaveSpacetime n} :
-- imply
  0 ≤ energyDensity φ p := by
-- proof
  unfold energyDensity
  apply mul_nonneg
  · norm_num
  · exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))

end CM14

namespace CM14

/--
[energyDensity_zero_derivs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energyDensity_zero_derivs
  {n : ℕ}
  {φ : WaveScalarField n}
  {t : ℝ}
  {x : Fin n → ℝ}
-- given
  (h : energyDensity φ (t, x) = 0) :
-- imply
  fderiv ℝ (fun s => φ (s, x)) t 1 = 0 ∧ ∀ i : Fin n, fderiv ℝ (fun y => φ (t, y)) x (Pi.single i 1) = 0 := by
-- proof
  unfold energyDensity at h
  have half_ne : (1/2 : ℝ) ≠ 0 := by norm_num
  have h1 := (mul_eq_zero.mp h).resolve_left half_ne
  have ha2 : (fderiv ℝ (fun s => φ (s, x)) t 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (fderiv ℝ (fun s => φ (s, x)) t 1),
      Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
        sq_nonneg (fderiv ℝ (fun y => φ (t, y)) x (Pi.single i 1)))]
  have hb_sum : ∑ j : Fin n, (fderiv ℝ (fun y => φ (t, y)) x (Pi.single j 1)) ^ 2 = 0 := by
    linarith
  constructor
  · nlinarith [ha2]
  · intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg (fderiv ℝ (fun y => φ (t, y)) x (Pi.single j 1)))).mp hb_sum i
        (Finset.mem_univ i)
    nlinarith [this]

end CM14

namespace CM14

/--
[energy_coercivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energy_coercivity
  {n : ℕ}
  {φ : WaveScalarField n}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
-- given
  (hφ : ContDiff ℝ 2 φ)
  (hR : 0 < R)
  (hφ_zero_init : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ (0, x) = 0)
  (hE : ∀ t, 0 ≤ t → t ≤ R → energyOnBall φ t x₀ (R - t) = 0) :
-- imply
  ∀ t, 0 ≤ t → t ≤ R → ∀ x, waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 → φ (t, x) = 0 := by
-- proof
  have h_density_zero : ∀ t, 0 ≤ t → t ≤ R →
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
      waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 → energyDensity φ (t, x) = 0 := by
    intro t ht0 htR
    have hEt := hE t ht0 htR
    have hnn : ∀ x : Fin n → ℝ,
      0 ≤ (if waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2
        then energyDensity φ (t, x) else 0) := by
      intro x; by_cases h : waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2
      · simp [h]; exact energyDensity_nonneg φ (t, x)
      · simp [h]
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall hnn)
      (energyDensity_integrable_on_ball φ hφ t x₀ (R - t))).mp hEt
    filter_upwards [hae] with x hx hball
    simp [hball] at hx
    exact hx
  have hdt : ∀ t, 0 ≤ t → t ≤ R →
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
      waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 →
      fderiv ℝ (fun s => φ (s, x)) t 1 = 0 := by
    intro t ht0 htR
    filter_upwards [h_density_zero t ht0 htR] with x hx hball
    exact (energyDensity_zero_derivs φ t x (hx hball)).1
  have hdx : ∀ t, 0 ≤ t → t ≤ R →
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
      waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 →
      ∀ i : Fin n, fderiv ℝ (fun y => φ (t, y)) x (Pi.single i 1) = 0 := by
    intro t ht0 htR
    filter_upwards [h_density_zero t ht0 htR] with x hx hball
    exact (energyDensity_zero_derivs φ t x (hx hball)).2
  intro t ht0 htR x hx
  exact zero_derivs_ae_imply_zero_field φ hφ x₀ R hR hφ_zero_init hdt hdx t ht0 htR x hx

end CM14

namespace CM14

/--
[waveOp_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma waveOp_sub
  {n : ℕ}
  {φ₁ φ₂ : WaveScalarField n}
  {p : WaveSpacetime n}
-- given
  (hφ₁ : ContDiff ℝ 2 φ₁)
  (hφ₂ : ContDiff ℝ 2 φ₂) :
-- imply
  waveOp (fun q => φ₁ q - φ₂ q) p = waveOp φ₁ p - waveOp φ₂ p :=
-- proof
  waveOp_linearity_sub φ₁ φ₂ hφ₁ hφ₂ p

end CM14

namespace CM14

/--
[energyOnBall_zero_of_same_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energyOnBall_zero_of_same_data
  {n : ℕ}
  {φ₁ φ₂ : WaveScalarField n}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
-- given
  (hφ₁ : ContDiff ℝ 2 φ₁)
  (hφ₂ : ContDiff ℝ 2 φ₂)
  (hR : 0 < R)
  (h_data : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ₁ (0, x) = φ₂ (0, x))
  (h_vel : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → fderiv ℝ (fun s => φ₁ (s, x)) 0 1 = fderiv ℝ (fun s => φ₂ (s, x)) 0 1) :
-- imply
  energyOnBall (fun q => φ₁ q - φ₂ q) 0 x₀ R = 0 :=
-- proof
  same_data_zero_energy φ₁ φ₂ hφ₁ hφ₂ x₀ R hR h_data h_vel

end CM14

namespace CM14

/--
[energyOnBall_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma energyOnBall_nonneg
  {n : ℕ}
  {φ : WaveScalarField n}
  {t : ℝ}
  {x₀ : Fin n → ℝ}
  {R : ℝ} :
-- imply
  0 ≤ energyOnBall φ t x₀ R := by
-- proof
  unfold energyOnBall
  apply integral_nonneg
  intro x
  simp only [Pi.zero_apply]
  split_ifs with h
  · unfold energyDensity
    apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
    apply add_nonneg (sq_nonneg _)
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · exact le_refl _

end CM14

namespace CM14

/--
[zero_energy_implies_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean)
-/
@[path]
lemma zero_energy_implies_zero
  {n : ℕ}
  {φ : WaveScalarField n}
  {x₀ : Fin n → ℝ}
  {R : ℝ}
-- given
  (hφ : ContDiff ℝ 2 φ)
  (hR : 0 < R)
  (hφ_zero_init : ∀ x, waveEuclidNormSq (x - x₀) ≤ R ^ 2 → φ (0, x) = 0)
  (hE : ∀ t, 0 ≤ t → t ≤ R → energyOnBall φ t x₀ (R - t) = 0) :
-- imply
  ∀ t, 0 ≤ t → t ≤ R → ∀ x, waveEuclidNormSq (x - x₀) ≤ (R - t) ^ 2 → φ (t, x) = 0 :=
-- proof
  energy_coercivity φ hφ x₀ R hR hφ_zero_init hE

end CM14


-- created on 2026-10-23
