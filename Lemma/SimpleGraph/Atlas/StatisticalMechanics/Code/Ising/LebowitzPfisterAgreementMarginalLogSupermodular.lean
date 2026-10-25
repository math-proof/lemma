import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementMarginalLogSupermodular
open Finset StatMech StatMech.Ising


/--
[ghsiAgreementMarginalProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalLogSupermodular.lean)
-/
@[path]
private lemma ghsiAgreementMarginalProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M P : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  0 <= ghsiAgreementMarginalProb G K hf M P := by
-- proof
  apply StatMech.Ising.ghsiAgreementMarginalProb_nonneg G K hf M P

/--
[ghsiAgreementMarginalProb_sum_powerset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalLogSupermodular.lean)
-/
@[path]
private lemma ghsiAgreementMarginalProb_sum_powerset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  (∑ P ∈ M.powerset, ghsiAgreementMarginalProb G K hf M P) = 1 := by
-- proof
  apply StatMech.Ising.ghsiAgreementMarginalProb_sum_powerset G K hf M

/--
[ghsiAgreementMarginalProb_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalLogSupermodular.lean)
-/
@[path]
private lemma ghsiAgreementMarginalProb_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M P Q : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hPM : P ⊆ M)
  (hQM : Q ⊆ M) :
-- imply
  ghsiAgreementMarginalProb G K hf M P * ghsiAgreementMarginalProb G K hf M Q <= ghsiAgreementMarginalProb G K hf M (P ∩ Q) * ghsiAgreementMarginalProb G K hf M (P ∪ Q) := by
-- proof
  apply StatMech.Ising.ghsiAgreementMarginalProb_logSupermodular G K hf hK hhf hPM hQM

/--
[ghsiAgreementMarginalProb_compl_ratio_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalLogSupermodular.lean)
-/
@[path]
private lemma ghsiAgreementMarginalProb_compl_ratio_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M P Q : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hPQ : P ⊆ Q)
  (hQM : Q ⊆ M) :
-- imply
  ghsiAgreementMarginalProb G K hf M P * ghsiAgreementMarginalProb G K hf M (M \ Q) <= ghsiAgreementMarginalProb G K hf M Q * ghsiAgreementMarginalProb G K hf M (M \ P) := by
-- proof
  apply StatMech.Ising.ghsiAgreementMarginalProb_compl_ratio_mono G K hf hK hhf hPQ hQM

/--
[ghsiAgreementMarginalProb_weightedCut_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalLogSupermodular.lean)
-/
@[path]
private lemma ghsiAgreementMarginalProb_weightedCut_sum_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : Finset V}
  {cuts : Finset I}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (weight : I -> Real)
  (P Q : I -> Finset V)
  (hweight : forall i, i ∈ cuts -> 0 <= weight i)
  (hP : forall i, i ∈ cuts -> P i ⊆ M)
  (hQ : forall i, i ∈ cuts -> Q i ⊆ M) :
-- imply
  (∑ i ∈ cuts, weight i * (ghsiAgreementMarginalProb G K hf M (P i) * ghsiAgreementMarginalProb G K hf M (Q i))) <= ∑ i ∈ cuts, weight i * (ghsiAgreementMarginalProb G K hf M (P i ∩ Q i) * ghsiAgreementMarginalProb G K hf M (P i ∪ Q i)) := by
-- proof
  apply StatMech.Ising.ghsiAgreementMarginalProb_weightedCut_sum_le G K hf hK hhf M cuts weight P Q hweight hP hQ

/--
[ghsiAgreementMarginalProb_weightedComplRatio_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalLogSupermodular.lean)
-/
@[path]
private lemma ghsiAgreementMarginalProb_weightedComplRatio_sum_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : Finset V}
  {cuts : Finset I}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (weight : I -> Real)
  (P Q : I -> Finset V)
  (hweight : forall i, i ∈ cuts -> 0 <= weight i)
  (hPQ : forall i, i ∈ cuts -> P i ⊆ Q i)
  (hQM : forall i, i ∈ cuts -> Q i ⊆ M) :
-- imply
  (∑ i ∈ cuts, weight i * (ghsiAgreementMarginalProb G K hf M (P i) * ghsiAgreementMarginalProb G K hf M (M \ Q i))) <= ∑ i ∈ cuts, weight i * (ghsiAgreementMarginalProb G K hf M (Q i) * ghsiAgreementMarginalProb G K hf M (M \ P i)) := by
-- proof
  apply StatMech.Ising.ghsiAgreementMarginalProb_weightedComplRatio_sum_le G K hf hK hhf M cuts weight P Q hweight hPQ hQM


-- created on 2026-10-23
