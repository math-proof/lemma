import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementComplementRatio
open Finset StatMech StatMech.Ising


/--
[ghsiSubsetMass_agreeFinset_eq_mul_fibreMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementComplementRatio.lean)
-/
@[path]
private lemma ghsiSubsetMass_agreeFinset_eq_mul_fibreMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ConfigSpace V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ghsiSubsetMass G K hf (ghsLAgreeFinset q) = (4 * Fintype.card (ConfigSpace V)) * ghsiFibreMass G K hf q := by
-- proof
  apply StatMech.Ising.ghsiSubsetMass_agreeFinset_eq_mul_fibreMass G K hf q

/--
[ghsiTZ_mul_ghsiUZ_le_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementComplementRatio.lean)
-/
@[path]
private lemma ghsiTZ_mul_ghsiUZ_le_of_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hAB : A ⊆ B) :
-- imply
  ghsiTZ G K hf A * ghsiUZ G K B <= ghsiTZ G K hf B * ghsiUZ G K A := by
-- proof
  apply StatMech.Ising.ghsiTZ_mul_ghsiUZ_le_of_subset G K hf hK hhf hAB

/--
[ghsiSubsetMass_compl_ratio_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementComplementRatio.lean)
-/
@[path]
private lemma ghsiSubsetMass_compl_ratio_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hAB : A ⊆ B) :
-- imply
  ghsiSubsetMass G K hf A * ghsiSubsetMass G K hf Bᶜ <= ghsiSubsetMass G K hf B * ghsiSubsetMass G K hf Aᶜ := by
-- proof
  apply StatMech.Ising.ghsiSubsetMass_compl_ratio_mono G K hf hK hhf hAB

/--
[ghsiFibreMass_compl_ratio_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementComplementRatio.lean)
-/
@[path]
private lemma ghsiFibreMass_compl_ratio_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q r : ConfigSpace V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hqr : q <= r) :
-- imply
  ghsiFibreMass G K hf q * ghsiFibreMass G K hf (fun x => !(r x)) <= ghsiFibreMass G K hf r * ghsiFibreMass G K hf (fun x => !(q x)) := by
-- proof
  apply StatMech.Ising.ghsiFibreMass_compl_ratio_mono G K hf hK hhf hqr


-- created on 2026-10-23
