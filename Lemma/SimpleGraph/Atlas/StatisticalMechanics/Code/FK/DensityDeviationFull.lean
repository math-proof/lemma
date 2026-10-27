import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.DensityDeviationFull.Part2
open StatMech StatMech.FK


/--
[chOpenCount_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean)
-/
@[path]
private lemma chOpenCount_eq_sum_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  (chOpenCount G ω : ℝ) = ∑ e ∈ G.edgeFinset, (if ω e = true then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.FK.chOpenCount_eq_sum_indicator G ω

/--
[fkMeanOpenCount_eq_sum_marginals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean)
-/
@[path]
private lemma fkMeanOpenCount_eq_sum_marginals_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ} :
-- imply
  fkMeanOpenCount G p q = ∑ e ∈ G.edgeFinset, edgeMarginalOpen G p q e := by
-- proof
  apply StatMech.FK.fkMeanOpenCount_eq_sum_marginals G p q

/--
[fkMeanOpenCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean)
-/
@[path]
private lemma fkMeanOpenCount_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  fkMeanOpenCount G p q ≤ p * (G.edgeFinset.card : ℝ) := by
-- proof
  apply StatMech.FK.fkMeanOpenCount_le G hp hp1 hq

/--
[fkMeanOpenCount_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean)
-/
@[path]
private lemma fkMeanOpenCount_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  p / (p + q * (1 - p)) * (G.edgeFinset.card : ℝ) ≤ fkMeanOpenCount G p q := by
-- proof
  apply StatMech.FK.fkMeanOpenCount_ge G hp hp1 hq

/--
[fkMeanOpenCount_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean)
-/
@[path]
private lemma fkMeanOpenCount_le_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkMeanOpenCount G p q ≤ (G.edgeFinset.card : ℝ) := by
-- proof
  apply StatMech.FK.fkMeanOpenCount_le_card G hp hp1 hq

/--
[reverse_markov_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean)
-/
@[path]
private lemma reverse_markov_upper_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype Ω]
  {w X : Ω → ℝ}
  {M μ ε : ℝ}
-- given
  (hw : ∀ ω, 0 ≤ w ω)
  (hsum : ∑ ω, w ω = 1)
  (hX0 : ∀ ω, 0 ≤ X ω)
  (hmean : ∑ ω, X ω * w ω ≤ μ * M)
  (hμ : 0 ≤ μ)
  (hε : 0 < ε)
  (hM : 0 < M) :
-- imply
  ε / (μ + ε) ≤ ∑ ω ∈ Finset.univ.filter (fun ω => X ω ≤ (μ + ε) * M), w ω := by
-- proof
  apply StatMech.FK.reverse_markov_upper G w X hw hsum hX0 hmean hμ hε hM

/--
[reverse_markov_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean)
-/
@[path]
private lemma reverse_markov_lower_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype Ω]
  {w X : Ω → ℝ}
  {M : ℝ}
  {ν ε : ℝ}
-- given
  (hw : ∀ ω, 0 ≤ w ω)
  (hsum : ∑ ω, w ω = 1)
  (hXM : ∀ ω, X ω ≤ M)
  (hmean : ν * M ≤ ∑ ω, X ω * w ω)
  (hν1 : ν ≤ 1)
  (hε : 0 < ε)
  (hM : 0 < M) :
-- imply
  ε / (1 - ν + ε) ≤ ∑ ω ∈ Finset.univ.filter (fun ω => (ν - ε) * M ≤ X ω), w ω := by
-- proof
  apply StatMech.FK.reverse_markov_lower G w X hw hsum hXM hmean hν1 hε hM

/--
[den_openCount_upper_deviation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean)
-/
@[path]
private lemma den_openCount_upper_deviation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ε : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hε : 0 < ε)
  (hεa : ε ≤ 1 - p)
  (hEpos : 0 < (G.edgeFinset.card : ℝ)) :
-- imply
  ε ≤ fkOpenCountLeProb G p q ((p + ε) * (G.edgeFinset.card : ℝ)) := by
-- proof
  apply StatMech.FK.den_openCount_upper_deviation G hp hp1 hq hε hεa hEpos

/--
[den_openCount_lower_deviation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean)
-/
@[path]
private lemma den_openCount_lower_deviation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ε : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hε : 0 < ε)
  (hεb : ε ≤ p / (p + q * (1 - p)))
  (hEpos : 0 < (G.edgeFinset.card : ℝ)) :
-- imply
  ε ≤ fkOpenCountGeProb G p q ((p / (p + q * (1 - p)) - ε) * (G.edgeFinset.card : ℝ)) := by
-- proof
  apply StatMech.FK.den_openCount_lower_deviation G hp hp1 hq hε hεb hEpos


-- created on 2026-10-23
