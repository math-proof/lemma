import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.OSFKSubcriticalClose
open Finset Real Set Filter Topology StatMech StatMech.OSSS StatMech.OSSS.OSFKSubcriticalClose


/--
[ofs_fk_q2_subcritical_decay_connEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKSubcriticalClose.lean)
-/
@[path]
private lemma ofs_fk_q2_subcritical_decay_connEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {a b κ : ℝ}
-- given
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hθub : ∀ s ∈ Icc a b, fkProbOf G s 2 (connEvent G x y) ≤ 1 - κ) :
-- imply
  fkProbOf G a 2 (connEvent G x y) ≤ Real.exp (-(4 * κ * (b - a))) := by
-- proof
  apply StatMech.OSSS.OSFKSubcriticalClose.ofs_fk_q2_subcritical_decay_connEvent G x y a b κ hab ha0 hb1 hκ hθub

/--
[ofs_subcritical_bound_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKSubcriticalClose.lean)
-/
@[path]
private lemma ofs_subcritical_bound_satisfiable_eq
  [Fintype V]
  [DecidableEq V]
  {x y : V}
  {s : ℝ}
-- given
  (hxy : x ≠ y) :
-- imply
  fkProbOf (⊥ : SimpleGraph V) s 2 (connEvent ⊥ x y) = 0 := by
-- proof
  apply StatMech.OSSS.OSFKSubcriticalClose.ofs_subcritical_bound_satisfiable hxy s

/--
[ofs_decay_self_at_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKSubcriticalClose.lean)
-/
@[path]
private lemma ofs_decay_self_at_diagonal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {s : ℝ}
-- given
  (hs : 0 < s)
  (hs1 : s < 1) :
-- imply
  fkProbOf G s 2 (connEvent G x x) = 1 := by
-- proof
  apply StatMech.OSSS.OSFKSubcriticalClose.ofs_decay_self_at_diagonal G x hs hs1

/--
[ofs_supercritical_meanField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKSubcriticalClose.lean)
-/
@[path]
private lemma ofs_supercritical_meanField_eq
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
  apply StatMech.OSSS.OSFKSubcriticalClose.ofs_supercritical_meanField T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound

/--
[ofs_betaC_eq_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKSubcriticalClose.lean)
-/
@[path]
private lemma ofs_betaC_eq_threshold_eq
  [Fintype V]
  [DecidableEq V]
  {Θ : ℝ → ℝ}
  {β₁ : ℝ}
-- given
  (hP1 : ∀ b₀, b₀ < β₁ → Θ b₀ = 0)
  (hP2 : ∀ b₀, β₁ < b₀ → 0 < Θ b₀) :
-- imply
  sSup (bcm_subcriticalSet Θ) = β₁ := by
-- proof
  apply StatMech.OSSS.OSFKSubcriticalClose.ofs_betaC_eq_threshold Θ β₁ hP1 hP2

/--
[ofs_fk_q2_sharpness_connEvent_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKSubcriticalClose.lean)
-/
@[path]
private lemma ofs_fk_q2_sharpness_connEvent_minimal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {a b κ : ℝ}
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β' β fβ fβ' m : ℝ}
  {Θ : ℝ → ℝ}
  {β₁ : ℝ}
-- given
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hθub : ∀ s ∈ Icc a b, fkProbOf G s 2 (connEvent G x y) ≤ 1 - κ)
  (hββ : β' ≤ β)
  (hm1 : 1 ≤ m)
  (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
  (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
  (hmlim : Tendsto mseq atTop (𝓝 m))
  (hboundMF : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β')
  (hP1 : ∀ b₀, b₀ < β₁ → Θ b₀ = 0)
  (hP2 : ∀ b₀, β₁ < b₀ → 0 < Θ b₀) :
-- imply
  (fkProbOf G a 2 (connEvent G x y) ≤ Real.exp (-(4 * κ * (b - a)))) ∧ (β - β' ≤ fβ - fβ') ∧ sSup (bcm_subcriticalSet Θ) = β₁ := by
-- proof
  apply StatMech.OSSS.OSFKSubcriticalClose.ofs_fk_q2_sharpness_connEvent_minimal G x y a b κ hab ha0 hb1 hκ hθub T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hboundMF Θ β₁ hP1 hP2

/--
[ofs_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OSFKSubcriticalClose.lean)
-/
@[path]
private lemma ofs_summary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {a b κ : ℝ}
-- given
  (hxy : x ≠ y)
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hθub : ∀ s ∈ Icc a b, fkProbOf G s 2 (connEvent G x y) ≤ 1 - κ) :
-- imply
  (fkProbOf G a 2 (connEvent G x y) ≤ Real.exp (-(4 * κ * (b - a)))) ∧ (fkProbOf (⊥ : SimpleGraph V) a 2 (connEvent ⊥ x y) = 0) := by
-- proof
  apply StatMech.OSSS.OSFKSubcriticalClose.ofs_summary G x y hxy a b κ hab ha0 hb1 hκ hθub


-- created on 2026-10-23
