import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.FKSharpnessAssembly
open Finset Real Set Filter Topology StatMech StatMech.OSSS


/--
[lind_var_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessAssembly.lean)
-/
@[path]
private lemma lind_var_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hf : ∀ ω, f ω = 0 ∨ f ω = 1) :
-- imply
  Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) := by
-- proof
  apply StatMech.OSSS.lind_var_indicator f hf

/--
[fk_poincare_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessAssembly.lean)
-/
@[path]
private lemma fk_poincare_indicator_eq
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
  apply StatMech.OSSS.fk_poincare_indicator G hp hp1 hq A hA

/--
[fk_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessAssembly.lean)
-/
@[path]
private lemma fk_differential_inequality_eq
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
  (hA : IsIncreasing A)
  (hbridge : ∑ e, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) = ∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)) :
-- imply
  russoPrefactor p * (fkProbOf G p q A * (1 - fkProbOf G p q A)) ≤ deriv (fun p => fkProbOf G p q A) p := by
-- proof
  apply StatMech.OSSS.fk_differential_inequality G hp hp1 hq A hA hbridge

/--
[fk_subcritical_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessAssembly.lean)
-/
@[path]
private lemma fk_subcritical_decay_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
  {a b κ : ℝ}
  {rate : ℝ}
-- given
  (hq : 1 ≤ q)
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hdi : ∀ x ∈ Icc a b, russoPrefactor x * (fkProbOf G x q A * (1 - fkProbOf G x q A)) ≤ deriv (fun p => fkProbOf G p q A) x)
  (hθub : ∀ x ∈ Icc a b, fkProbOf G x q A ≤ 1 - κ)
  (hrate : 0 < rate)
  (hrlb : ∀ x ∈ Icc a b, rate ≤ russoPrefactor x * κ) :
-- imply
  fkProbOf G a q A ≤ Real.exp (-(rate * (b - a))) := by
-- proof
  apply StatMech.OSSS.fk_subcritical_decay G hq A a b κ hab ha0 hb1 hκ hdi hθub rate hrate hrlb

/--
[fk_q2_crossing_decay_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessAssembly.lean)
-/
@[path]
private lemma fk_q2_crossing_decay_poincare_eq
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
  (hbridge : ∀ p ∈ Icc a b, ∑ e, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) = ∑ e ∈ G.edgeFinset, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
  (hθub : ∀ p ∈ Icc a b, fkProbOf G p 2 A ≤ 1 - κ) :
-- imply
  fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a))) := by
-- proof
  apply StatMech.OSSS.fk_q2_crossing_decay_poincare G A hA a b κ hab ha0 hb1 hκ hbridge hθub

/--
[fk_meanField_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessAssembly.lean)
-/
@[path]
private lemma fk_meanField_lower_eq
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
  apply StatMech.OSSS.fk_meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound

/--
[fk_sharpness_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessAssembly.lean)
-/
@[path]
private lemma fk_sharpness_both_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
  {a b κ : ℝ}
  {rate : ℝ}
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β' β fβ fβ' m : ℝ}
-- given
  (hq : 1 ≤ q)
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hdi : ∀ x ∈ Icc a b, russoPrefactor x * (fkProbOf G x q A * (1 - fkProbOf G x q A)) ≤ deriv (fun p => fkProbOf G p q A) x)
  (hθub : ∀ x ∈ Icc a b, fkProbOf G x q A ≤ 1 - κ)
  (hrate : 0 < rate)
  (hrlb : ∀ x ∈ Icc a b, rate ≤ russoPrefactor x * κ)
  (hββ : β' ≤ β)
  (hm1 : 1 ≤ m)
  (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
  (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
  (hmlim : Tendsto mseq atTop (𝓝 m))
  (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
-- imply
  (fkProbOf G a q A ≤ Real.exp (-(rate * (b - a)))) ∧ (β - β' ≤ fβ - fβ') := by
-- proof
  apply StatMech.OSSS.fk_sharpness_both G hq A a b κ hab ha0 hb1 hκ hdi hθub rate hrate hrlb T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound

/--
[potts_decay_of_fk_sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessAssembly.lean)
-/
@[path]
private lemma potts_decay_of_fk_sharpness_eq
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
  apply StatMech.OSSS.potts_decay_of_fk_sharpness q hq c pottsCorr θ hES hθ_nonneg hθ_decay


-- created on 2026-10-23
