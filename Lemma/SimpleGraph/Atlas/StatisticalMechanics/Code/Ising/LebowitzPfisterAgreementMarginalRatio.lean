import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementMarginalRatio.Part2
open Finset StatMech StatMech.Ising


/--
[ghsiSubsetMass_mul_compl_le_interCompl_mul_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalRatio.lean)
-/
@[path]
private lemma ghsiSubsetMass_mul_compl_le_interCompl_mul_union_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  ghsiSubsetMass G K hf A * ghsiSubsetMass G K hf Bᶜ <= ghsiSubsetMass G K hf (A ∩ B)ᶜ * ghsiSubsetMass G K hf (A ∪ B) := by
-- proof
  apply StatMech.Ising.ghsiSubsetMass_mul_compl_le_interCompl_mul_union G K hf hK hhf A B

/--
[ghsiSubsetMarginalMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalRatio.lean)
-/
@[path]
private lemma ghsiSubsetMarginalMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M P : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  0 <= ghsiSubsetMarginalMass G K hf M P := by
-- proof
  apply StatMech.Ising.ghsiSubsetMarginalMass_nonneg G K hf M P

/--
[sum_ghsiSubsetMass_compl_eq_marginal_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalRatio.lean)
-/
@[path]
private lemma sum_ghsiSubsetMass_compl_eq_marginal_sdiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M P : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hPM : P ⊆ M) :
-- imply
  (∑ S ∈ Mᶜ.powerset, ghsiSubsetMass G K hf (P ∪ S)ᶜ) = ghsiSubsetMarginalMass G K hf M (M \ P) := by
-- proof
  apply StatMech.Ising.sum_ghsiSubsetMass_compl_eq_marginal_sdiff G K hf hPM

/--
[ghsiSubsetMarginalMass_compl_ratio_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalRatio.lean)
-/
@[path]
private lemma ghsiSubsetMarginalMass_compl_ratio_mono_eq
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
  ghsiSubsetMarginalMass G K hf M P * ghsiSubsetMarginalMass G K hf M (M \ Q) <= ghsiSubsetMarginalMass G K hf M Q * ghsiSubsetMarginalMass G K hf M (M \ P) := by
-- proof
  apply StatMech.Ising.ghsiSubsetMarginalMass_compl_ratio_mono G K hf hK hhf hPQ hQM

/--
[ghsiSubsetMarginalMass_rank_zero_three_le_one_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalRatio.lean)
-/
@[path]
private lemma ghsiSubsetMarginalMass_rank_zero_three_le_one_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  ghsiSubsetMarginalMass G K hf M ∅ * (∑ x ∈ M, ghsiSubsetMarginalMass G K hf M (M \ {x})) <= (∑ x ∈ M, ghsiSubsetMarginalMass G K hf M {x}) * ghsiSubsetMarginalMass G K hf M M := by
-- proof
  apply StatMech.Ising.ghsiSubsetMarginalMass_rank_zero_three_le_one_four G K hf hK hhf M


-- created on 2026-10-23
