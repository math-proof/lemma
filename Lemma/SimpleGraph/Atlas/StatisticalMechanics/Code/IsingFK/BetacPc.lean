import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.BetacPc.Part3
open Real StatMech StatMech.IsingFK


/--
[pToBeta_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma pToBeta_two_eq
  {p : ℝ} :
-- imply
  pToBeta 2 p = -(1 / 2) * Real.log (1 - p) := by
-- proof
  apply StatMech.IsingFK.pToBeta_two p

/--
[betaToP_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma betaToP_two_eq
  {β : ℝ} :
-- imply
  betaToP 2 β = 1 - Real.exp (-2 * β) := by
-- proof
  apply StatMech.IsingFK.betaToP_two β

/--
[betaToP_pToBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma betaToP_pToBeta_eq
  {q p : ℝ}
-- given
  (hq0 : q ≠ 0)
  (hq1 : q ≠ 1)
  (hp : p < 1) :
-- imply
  betaToP q (pToBeta q p) = p := by
-- proof
  apply StatMech.IsingFK.betaToP_pToBeta q p hq0 hq1 hp

/--
[pToBeta_betaToP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma pToBeta_betaToP_eq
  {q β : ℝ}
-- given
  (hq0 : q ≠ 0)
  (hq1 : q ≠ 1) :
-- imply
  pToBeta q (betaToP q β) = β := by
-- proof
  apply StatMech.IsingFK.pToBeta_betaToP q β hq0 hq1

/--
[strictMonoOn_pToBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma strictMonoOn_pToBeta_eq
  {q : ℝ}
-- given
  (hq : 1 < q) :
-- imply
  StrictMonoOn (pToBeta q) (Set.Iio 1) := by
-- proof
  apply StatMech.IsingFK.strictMonoOn_pToBeta q hq

/--
[strictMono_betaToP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma strictMono_betaToP_eq
  {q : ℝ}
-- given
  (hq : 1 < q) :
-- imply
  StrictMono (betaToP q) := by
-- proof
  apply StatMech.IsingFK.strictMono_betaToP q hq

/--
[betaToP_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma betaToP_mem_eq
  {q β : ℝ}
-- given
  (hq : 1 < q)
  (hβ : 0 ≤ β) :
-- imply
  betaToP q β ∈ Set.Ico (0 : ℝ) 1 := by
-- proof
  apply StatMech.IsingFK.betaToP_mem q β hq hβ

/--
[pToBeta_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma pToBeta_mem_eq
  {q p : ℝ}
-- given
  (hq : 1 < q)
  (hp : p ∈ Set.Ico (0 : ℝ) 1) :
-- imply
  pToBeta q p ∈ Set.Ici (0 : ℝ) := by
-- proof
  apply StatMech.IsingFK.pToBeta_mem q p hq hp

/--
[pToBeta_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma pToBeta_zero_eq
  {q : ℝ} :
-- imply
  pToBeta q 0 = 0 := by
-- proof
  apply StatMech.IsingFK.pToBeta_zero q

/--
[betaToP_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma betaToP_zero_eq
  {q : ℝ} :
-- imply
  betaToP q 0 = 0 := by
-- proof
  apply StatMech.IsingFK.betaToP_zero q

/--
[betaToP_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma betaToP_bijOn_eq
  {q : ℝ}
-- given
  (hq : 1 < q) :
-- imply
  Set.BijOn (betaToP q) (Set.Ici 0) (Set.Ico 0 1) := by
-- proof
  apply StatMech.IsingFK.betaToP_bijOn q hq

/--
[pToBeta_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma pToBeta_bijOn_eq
  {q : ℝ}
-- given
  (hq : 1 < q) :
-- imply
  Set.BijOn (pToBeta q) (Set.Ico 0 1) (Set.Ici 0) := by
-- proof
  apply StatMech.IsingFK.pToBeta_bijOn q hq

/--
[mem_zeroMagnetizationSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma mem_zeroMagnetizationSet_eq
  {mStar : ℝ → ℝ}
  {β : ℝ} :
-- imply
  β ∈ {β : ℝ | 0 < β ∧ mStar β = 0} ↔ 0 < β ∧ mStar β = 0 := by
-- proof
  apply StatMech.IsingFK.mem_zeroMagnetizationSet

/--
[betaC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma betaC_eq_eq
  {mStar : ℝ → ℝ}
  {q pc : ℝ}
-- given
  (hnonneg : ∀ β, 0 ≤ mStar β)
  (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β))
  (hpos : 0 < pToBeta q pc) :
-- imply
  betaC mStar = pToBeta q pc := by
-- proof
  apply StatMech.IsingFK.betaC_eq mStar q pc hnonneg hpos_iff hpos

/--
[betaC_eq_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma betaC_eq_log_eq
  {mStar : ℝ → ℝ}
  {q pc : ℝ}
-- given
  (hnonneg : ∀ β, 0 ≤ mStar β)
  (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β))
  (hpos : 0 < pToBeta q pc) :
-- imply
  betaC mStar = -((q - 1) / q) * Real.log (1 - pc) := by
-- proof
  apply StatMech.IsingFK.betaC_eq_log mStar q pc hnonneg hpos_iff hpos

/--
[magnetization_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma magnetization_pos_iff_eq
  {mStar : ℝ → ℝ}
  {q pc p : ℝ}
-- given
  (hq : 1 < q)
  (hp : p ∈ Set.Ico (0 : ℝ) 1)
  (hpc : pc ∈ Set.Ico (0 : ℝ) 1)
  (hβpos : 0 < pToBeta q p)
  (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β)) :
-- imply
  0 < mStar (pToBeta q p) ↔ pc < p := by
-- proof
  apply StatMech.IsingFK.magnetization_pos_iff mStar q pc p hq hp hpc hβpos hpos_iff

/--
[isingBetaC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean)
-/
@[path]
private lemma isingBetaC_eq_eq
  {d : ℕ}
-- given
  (hnonneg : ∀ β, 0 ≤ Ising.magnetization d β)
  (hpos_iff : ∀ β, 0 < β → (0 < Ising.magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
  (hpos : 0 < pToBeta 2 (FK.fkPc d 2)) :
-- imply
  isingBetaC d = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.IsingFK.isingBetaC_eq d hnonneg hpos_iff hpos


-- created on 2026-10-23
