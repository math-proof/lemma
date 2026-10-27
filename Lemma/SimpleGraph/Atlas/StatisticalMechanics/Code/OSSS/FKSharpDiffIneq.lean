import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpDiffIneq
open Real Filter Topology Set Finset StatMech StatMech.OSSS StatMech.OSSS.FKSharpDiffIneq


/--
[fkd_diff_ineq_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpDiffIneq.lean)
-/
@[path]
private lemma fkd_diff_ineq_pointwise_eq
  {n : ℕ}
  {cR Sg θ θ' S : ℝ}
-- given
  (hSg : 0 < Sg)
  (hcR : 0 ≤ cR)
  (hcov : ((n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ S)
  (hRusso : cR * S ≤ θ') :
-- imply
  (cR * (n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ θ' := by
-- proof
  apply StatMech.OSSS.FKSharpDiffIneq.fkd_diff_ineq_pointwise n cR Sg θ θ' S hSg hcR hcov hRusso

/--
[fkd_diff_ineq_pointwise_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpDiffIneq.lean)
-/
@[path]
private lemma fkd_diff_ineq_pointwise_weighted_eq
  [Fintype E]
  [Nonempty E]
  {n : ℕ}
  {Sg θ θ' : ℝ}
  {J Cov : E → ℝ}
  {β : ℝ}
-- given
  (hSg : 0 < Sg)
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hCov : ∀ e, 0 ≤ Cov e)
  (hderiv : θ' = ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e)
  (hcov : ((n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ ∑ e, Cov e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ (cR * (n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ θ' := by
-- proof
  apply StatMech.OSSS.FKSharpDiffIneq.fkd_diff_ineq_pointwise_weighted n Sg θ θ' J Cov β hSg hJ hβ hCov hderiv hcov

/--
[fkd_engine_rate_of_assembled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpDiffIneq.lean)
-/
@[path]
private lemma fkd_engine_rate_of_assembled_eq
  {n : ℕ}
  {cR Sg θ θ' Sn : ℝ}
-- given
  (hSg : 0 < Sg)
  (hcR : 0 < cR)
  (hSn : 0 < Sn)
  (hθ1 : θ < 1)
  (hident : Sn * (cR * (1 - θ)) = 4 * Sg)
  (hassembled : (cR * (n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ θ') :
-- imply
  ((n : ℝ) / Sn) * θ ≤ θ' := by
-- proof
  apply StatMech.OSSS.FKSharpDiffIneq.fkd_engine_rate_of_assembled n cR Sg θ θ' Sn hSg hcR hSn hθ1 hident hassembled

/--
[fk_q2_subcritical_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpDiffIneq.lean)
-/
@[path]
private lemma fk_q2_subcritical_decay_eq
  {θ θ' : ℕ → ℝ → ℝ}
  {α δ β M : ℝ}
  {N : ℕ}
-- given
  (hδ : 0 < δ)
  (hα : 0 < α)
  (hα1 : α ≤ 1)
  (hMnn : 0 ≤ M)
  (hN : 1 ≤ N)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
  (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
  (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
  (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → θ k y ≤ θ k x)
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
  (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, ((n : ℝ) / Sig θ n x) * θ n x ≤ θ' n x)
  (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.OSSS.FKSharpDiffIneq.fk_q2_subcritical_decay θ θ' α δ β M N hδ hα hα1 hMnn hN hd hθnn hθM hθmono hSpos hdiff hSpoly

/--
[fk_q2_meanField_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpDiffIneq.lean)
-/
@[path]
private lemma fk_q2_meanField_lower_eq
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β' β fβ fβ' m : ℝ}
-- given
  (hββ : β' ≤ β)
  (hm1 : 1 ≤ m)
  (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
  (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
  (hmlim : Tendsto mseq atTop (𝓝 m))
  (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
-- imply
  β - β' ≤ fβ - fβ' := by
-- proof
  apply StatMech.OSSS.FKSharpDiffIneq.fk_q2_meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound

/--
[fk_q2_sharp_differential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpDiffIneq.lean)
-/
@[path]
private lemma fk_q2_sharp_differential_eq
  {θ θ' : ℕ → ℝ → ℝ}
  {α δ β M : ℝ}
  {N : ℕ}
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β₂' β₂ fβ₂ fβ₂' m : ℝ}
-- given
  (hδ : 0 < δ)
  (hα : 0 < α)
  (hα1 : α ≤ 1)
  (hMnn : 0 ≤ M)
  (hN : 1 ≤ N)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
  (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
  (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
  (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → θ k y ≤ θ k x)
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
  (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, ((n : ℝ) / Sig θ n x) * θ n x ≤ θ' n x)
  (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α))
  (hββ : β₂' ≤ β₂)
  (hm1 : 1 ≤ m)
  (hTβ : Tendsto (fun n => T n β₂) atTop (𝓝 fβ₂))
  (hTβ' : Tendsto (fun n => T n β₂') atTop (𝓝 fβ₂'))
  (hmlim : Tendsto mseq atTop (𝓝 m))
  (hbound : ∀ᶠ n in atTop, (β₂ - β₂') * mseq n ≤ T n β₂ - T n β₂') :
-- imply
  (∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ))) ∧ (β₂ - β₂' ≤ fβ₂ - fβ₂') := by
-- proof
  apply StatMech.OSSS.FKSharpDiffIneq.fk_q2_sharp_differential θ θ' α δ β M N hδ hα hα1 hMnn hN hd hθnn hθM hθmono hSpos hdiff hSpoly T mseq β₂' β₂ fβ₂ fβ₂' m hββ hm1 hTβ hTβ' hmlim hbound

/--
[fk_q2_subcritical_decay_of_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpDiffIneq.lean)
-/
@[path]
private lemma fk_q2_subcritical_decay_of_cov_eq
  [Fintype E]
  [Nonempty E]
  {θ θ' : ℕ → ℝ → ℝ}
  {J : E → ℝ}
  {Cov : ℕ → ℝ → E → ℝ}
  {Sgn : ℕ → ℝ → ℝ}
  {cRf : ℕ → ℝ → ℝ}
  {α δ β M : ℝ}
  {N : ℕ}
-- given
  (hδ : 0 < δ)
  (hα : 0 < α)
  (hα1 : α ≤ 1)
  (hMnn : 0 ≤ M)
  (hN : 1 ≤ N)
  (hJ : ∀ e, 0 < J e)
  (hxpos : ∀ x ∈ Icc (β - 2 * δ) β, 0 < x)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
  (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
  (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
  (hθlt1 : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x < 1)
  (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → θ k y ≤ θ k x)
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
  (hSgnpos : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sgn n x)
  (hCovnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ∀ e, 0 ≤ Cov n x e)
  (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1)) * Cov n x e)
  (hcov : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ((n : ℝ) / (4 * Sgn n x)) * (θ n x * (1 - θ n x)) ≤ ∑ e, Cov n x e)
  (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
  (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, Sig θ n x * (cRf n x * (1 - θ n x)) = 4 * Sgn n x)
  (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.OSSS.FKSharpDiffIneq.fk_q2_subcritical_decay_of_cov θ θ' J Cov Sgn cRf α δ β M N hδ hα hα1 hMnn hN hJ hxpos hd hθnn hθM hθlt1 hθmono hSpos hSgnpos hCovnn hderiv hcov hcRf hident hSpoly

/--
[fk_q2_sharp_differential_of_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpDiffIneq.lean)
-/
@[path]
private lemma fk_q2_sharp_differential_of_cov_eq
  [Fintype E]
  [Nonempty E]
  {θ θ' : ℕ → ℝ → ℝ}
  {J : E → ℝ}
  {Cov : ℕ → ℝ → E → ℝ}
  {Sgn : ℕ → ℝ → ℝ}
  {cRf : ℕ → ℝ → ℝ}
  {α δ β M : ℝ}
  {N : ℕ}
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β₂' β₂ fβ₂ fβ₂' m : ℝ}
-- given
  (hδ : 0 < δ)
  (hα : 0 < α)
  (hα1 : α ≤ 1)
  (hMnn : 0 ≤ M)
  (hN : 1 ≤ N)
  (hJ : ∀ e, 0 < J e)
  (hxpos : ∀ x ∈ Icc (β - 2 * δ) β, 0 < x)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
  (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
  (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
  (hθlt1 : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x < 1)
  (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → θ k y ≤ θ k x)
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
  (hSgnpos : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sgn n x)
  (hCovnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ∀ e, 0 ≤ Cov n x e)
  (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1)) * Cov n x e)
  (hcov : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ((n : ℝ) / (4 * Sgn n x)) * (θ n x * (1 - θ n x)) ≤ ∑ e, Cov n x e)
  (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
  (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, Sig θ n x * (cRf n x * (1 - θ n x)) = 4 * Sgn n x)
  (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α))
  (hββ : β₂' ≤ β₂)
  (hm1 : 1 ≤ m)
  (hTβ : Tendsto (fun n => T n β₂) atTop (𝓝 fβ₂))
  (hTβ' : Tendsto (fun n => T n β₂') atTop (𝓝 fβ₂'))
  (hmlim : Tendsto mseq atTop (𝓝 m))
  (hbound : ∀ᶠ n in atTop, (β₂ - β₂') * mseq n ≤ T n β₂ - T n β₂') :
-- imply
  (∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ))) ∧ (β₂ - β₂' ≤ fβ₂ - fβ₂') := by
-- proof
  apply StatMech.OSSS.FKSharpDiffIneq.fk_q2_sharp_differential_of_cov θ θ' J Cov Sgn cRf α δ β M N hδ hα hα1 hMnn hN hJ hxpos hd hθnn hθM hθlt1 hθmono hSpos hSgnpos hCovnn hderiv hcov hcRf hident hSpoly T mseq β₂' β₂ fβ₂ fβ₂' m hββ hm1 hTβ hTβ' hmlim hbound


-- created on 2026-10-23
