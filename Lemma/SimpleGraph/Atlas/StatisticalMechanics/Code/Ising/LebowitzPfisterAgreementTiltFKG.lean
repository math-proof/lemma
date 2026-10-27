import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementTiltFKG
open Finset StatMech StatMech.Ising


/--
[replicaAgreementSpin_sup_add_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementTiltFKG.lean)
-/
@[path]
private lemma replicaAgreementSpin_sup_add_inf_eq
  [Fintype V]
  [DecidableEq V]
  {q s : ConfigSpace V}
-- given
  (sites : I -> V) :
-- imply
  replicaAgreementSpin sites (q ⊔ s) + replicaAgreementSpin sites (q ⊓ s) = replicaAgreementSpin sites q + replicaAgreementSpin sites s := by
-- proof
  apply StatMech.Ising.replicaAgreementSpin_sup_add_inf sites q s

/--
[replicaAgreementTiltFactor_logModular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementTiltFKG.lean)
-/
@[path]
private lemma replicaAgreementTiltFactor_logModular_eq
  [Fintype V]
  [DecidableEq V]
  {r : Real}
  {q s : ConfigSpace V}
-- given
  (sites : I -> V) :
-- imply
  Real.exp (r * replicaAgreementSpin sites q) * Real.exp (r * replicaAgreementSpin sites s) = Real.exp (r * replicaAgreementSpin sites (q ⊔ s)) * Real.exp (r * replicaAgreementSpin sites (q ⊓ s)) := by
-- proof
  apply StatMech.Ising.replicaAgreementTiltFactor_logModular sites r q s

/--
[replicaAgreementTiltProb_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementTiltFKG.lean)
-/
@[path]
private lemma replicaAgreementTiltProb_fkg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall x, 0 <= hf x)
  (sites : I -> V) :
-- imply
  FKGLatticeCondition (replicaAgreementTiltProb G J hf sites r) := by
-- proof
  apply StatMech.Ising.replicaAgreementTiltProb_fkg G J hf hJ hhf sites r

/--
[replicaAgreementTilt_fkg_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementTiltFKG.lean)
-/
@[path]
private lemma replicaAgreementTilt_fkg_inequality_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
  {f g : ConfigSpace V -> Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall x, 0 <= hf x)
  (sites : I -> V)
  (hfmono : Monotone f)
  (hgmono : Monotone g) :
-- imply
  (∑ q, replicaAgreementTiltProb G J hf sites r q * f q) * (∑ q, replicaAgreementTiltProb G J hf sites r q * g q) <= ∑ q, replicaAgreementTiltProb G J hf sites r q * (f q * g q) := by
-- proof
  apply StatMech.Ising.replicaAgreementTilt_fkg_inequality G J hf hJ hhf sites r hfmono hgmono


-- created on 2026-10-23
