import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementTiltRows
open Finset StatMech StatMech.Ising


/--
[replicaBridgeVariance_eq_sum_agreementTiltCovarianceRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementTiltRows.lean)
-/
@[path]
private lemma replicaBridgeVariance_eq_sum_agreementTiltCovarianceRow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeVariance G J hf sites r = ∑ i : I, replicaAgreementTiltCovarianceRow G J hf sites i r := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_eq_sum_agreementTiltCovarianceRow G J hf sites r

/--
[replicaBridgeVariance_le_neg_of_covarianceRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementTiltRows.lean)
-/
@[path]
private lemma replicaBridgeVariance_le_neg_of_covarianceRows_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V)
  (hrow : forall i, replicaAgreementTiltCovarianceRow G J hf sites i r <= replicaAgreementTiltCovarianceRow G J hf sites i (-r)) :
-- imply
  replicaBridgeVariance G J hf sites r <= replicaBridgeVariance G J hf sites (-r) := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_le_neg_of_covarianceRows G J hf sites r hrow


-- created on 2026-10-23
