import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementMarginalStrictPositivity
open Finset StatMech StatMech.Ising


/--
[ghsiAgreementProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalStrictPositivity.lean)
-/
@[path]
private lemma ghsiAgreementProb_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  0 < ghsiAgreementProb G K hf q := by
-- proof
  apply StatMech.Ising.ghsiAgreementProb_pos G K hf q

/--
[ghsiAgreementMarginalProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalStrictPositivity.lean)
-/
@[path]
private lemma ghsiAgreementMarginalProb_pos_eq
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
  0 < ghsiAgreementMarginalProb G K hf M P := by
-- proof
  apply StatMech.Ising.ghsiAgreementMarginalProb_pos G K hf hPM

/--
[mul_mul_le_of_cancellativeCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalStrictPositivity.lean)
-/
@[path]
private lemma mul_mul_le_of_cancellativeCuts_eq
  [Fintype V]
  [DecidableEq V]
  {x0 x1 x3 x12 x13 x15 : Real}
-- given
  (hx0 : 0 < x0)
  (hx12 : 0 < x12)
  (hx3 : 0 <= x3)
  (hx13 : 0 <= x13)
  (hlog : x1 * x12 <= x0 * x13)
  (hcompl : x0 * x3 <= x12 * x15) :
-- imply
  x1 * x3 <= x13 * x15 := by
-- proof
  apply StatMech.Ising.mul_mul_le_of_cancellativeCuts hx0 hx12 hx3 hx13 hlog hcompl

/--
[ghsiAgreementMarginalProb_disjoint_cancellativeCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalStrictPositivity.lean)
-/
@[path]
private lemma ghsiAgreementMarginalProb_disjoint_cancellativeCut_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M A B : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hAM : A ⊆ M)
  (hBM : B ⊆ M)
  (hAB : Disjoint A B) :
-- imply
  ghsiAgreementMarginalProb G K hf M A * ghsiAgreementMarginalProb G K hf M (M \ B) <= ghsiAgreementMarginalProb G K hf M (A ∪ B) * ghsiAgreementMarginalProb G K hf M M := by
-- proof
  apply StatMech.Ising.ghsiAgreementMarginalProb_disjoint_cancellativeCut G K hf hK hhf hAM hBM hAB


-- created on 2026-10-23
