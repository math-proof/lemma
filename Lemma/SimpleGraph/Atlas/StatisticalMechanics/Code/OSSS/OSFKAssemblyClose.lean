import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.OSFKAssemblyClose
open Finset Real Set Filter Topology StatMech StatMech.OSSS StatMech.OSSS.OSFKAssemblyClose


/--
[ofa_russoPrefactor_ge_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKAssemblyClose.lean)
-/
@[path]
private lemma ofa_russoPrefactor_ge_four_eq
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (4 : ℝ) ≤ russoPrefactor p := by
-- proof
  apply StatMech.OSSS.OSFKAssemblyClose.ofa_russoPrefactor_ge_four hp hp1

/--
[ofa_fk_q2_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKAssemblyClose.lean)
-/
@[path]
private lemma ofa_fk_q2_differential_inequality_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : IsIncreasing A)
  (hbridge : ∑ e, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) = ∑ e ∈ G.edgeFinset, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)) :
-- imply
  russoPrefactor p * (fkProbOf G p 2 A * (1 - fkProbOf G p 2 A)) ≤ deriv (fun p => fkProbOf G p 2 A) p := by
-- proof
  apply StatMech.OSSS.OSFKAssemblyClose.ofa_fk_q2_differential_inequality G hp hp1 A hA hbridge

/--
[ofa_fk_q2_subcritical_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKAssemblyClose.lean)
-/
@[path]
private lemma ofa_fk_q2_subcritical_decay_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Set (ConfigSpace (Sym2 V))}
  {a b κ : ℝ}
-- given
  (hA : IsIncreasing A)
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hbridge : ∀ x ∈ Icc a b, ∑ e, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) = ∑ e ∈ G.edgeFinset, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
  (hθub : ∀ x ∈ Icc a b, fkProbOf G x 2 A ≤ 1 - κ) :
-- imply
  fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a))) := by
-- proof
  apply StatMech.OSSS.OSFKAssemblyClose.ofa_fk_q2_subcritical_decay G A hA a b κ hab ha0 hb1 hκ hbridge hθub

/--
[ofa_fk_meanField_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKAssemblyClose.lean)
-/
@[path]
private lemma ofa_fk_meanField_lower_eq
  [Fintype V]
  [DecidableEq V]
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
  apply StatMech.OSSS.OSFKAssemblyClose.ofa_fk_meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound

/--
[ofa_betaC_eq_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKAssemblyClose.lean)
-/
@[path]
private lemma ofa_betaC_eq_threshold_eq
  [Fintype V]
  [DecidableEq V]
  {Θ : ℝ → ℝ}
  {β₁ : ℝ}
-- given
  (hP1 : ∀ β, β < β₁ → Θ β = 0)
  (hP2 : ∀ β, β₁ < β → 0 < Θ β) :
-- imply
  sSup (bcm_subcriticalSet Θ) = β₁ := by
-- proof
  apply StatMech.OSSS.OSFKAssemblyClose.ofa_betaC_eq_threshold Θ β₁ hP1 hP2

/--
[ofa_fk_q2_sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKAssemblyClose.lean)
-/
@[path]
private lemma ofa_fk_q2_sharpness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Set (ConfigSpace (Sym2 V))}
  {a b κ : ℝ}
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β' β fβ fβ' m : ℝ}
  {Θ : ℝ → ℝ}
  {β₁ : ℝ}
-- given
  (hA : IsIncreasing A)
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hbridge : ∀ x ∈ Icc a b, ∑ e, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) = ∑ e ∈ G.edgeFinset, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
  (hθub : ∀ x ∈ Icc a b, fkProbOf G x 2 A ≤ 1 - κ)
  (hββ : β' ≤ β)
  (hm1 : 1 ≤ m)
  (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
  (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
  (hmlim : Tendsto mseq atTop (𝓝 m))
  (hboundMF : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β')
  (hP1 : ∀ b₀, b₀ < β₁ → Θ b₀ = 0)
  (hP2 : ∀ b₀, β₁ < b₀ → 0 < Θ b₀) :
-- imply
  (fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a)))) ∧ (β - β' ≤ fβ - fβ') ∧ sSup (bcm_subcriticalSet Θ) = β₁ := by
-- proof
  apply StatMech.OSSS.OSFKAssemblyClose.ofa_fk_q2_sharpness G A hA a b κ hab ha0 hb1 hκ hbridge hθub T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hboundMF Θ β₁ hP1 hP2

/--
[ofa_potts_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKAssemblyClose.lean)
-/
@[path]
private lemma ofa_potts_decay_eq
  [Fintype V]
  [DecidableEq V]
  {q : ℝ}
  {c pottsCorr θ : ℝ}
-- given
  (hq : 2 ≤ q)
  (hES : pottsCorr = (q - 1) / q * θ)
  (hθ_nonneg : 0 ≤ θ)
  (hθ_decay : θ ≤ Real.exp (-c)) :
-- imply
  0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-c) := by
-- proof
  apply StatMech.OSSS.OSFKAssemblyClose.ofa_potts_decay q hq c pottsCorr θ hES hθ_nonneg hθ_decay

/--
[ofa_hcov_residueFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKAssemblyClose.lean)
-/
@[path]
private lemma ofa_hcov_residueFree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  fkProbOf G p q A * (1 - fkProbOf G p q A) ≤ ∑ e, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
-- proof
  apply StatMech.OSSS.OSFKAssemblyClose.ofa_hcov_residueFree G hp hp1 hq A hA

/--
[ofa_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKAssemblyClose.lean)
-/
@[path]
private lemma ofa_summary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Set (ConfigSpace (Sym2 V))}
  {a b κ : ℝ}
-- given
  (hA : IsIncreasing A)
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hbridge : ∀ x ∈ Icc a b, ∑ e, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) = ∑ e ∈ G.edgeFinset, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
  (hθub : ∀ x ∈ Icc a b, fkProbOf G x 2 A ≤ 1 - κ) :
-- imply
  (fkProbOf G a 2 A * (1 - fkProbOf G a 2 A) ≤ ∑ e, fkCov G a 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)) ∧ (fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a)))) := by
-- proof
  apply StatMech.OSSS.OSFKAssemblyClose.ofa_summary G A hA a b κ hab ha0 hb1 hκ hbridge hθub


-- created on 2026-10-23
