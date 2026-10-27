import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteHamiltonian.Part4
open Matrix StatMech StatMech.FrontierA


/--
[quantumIsingDisagreementSet_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingDisagreementSet_comm_eq
  {L : Nat}
  {sigma tau : QuantumIsingChainConfig L} :
-- imply
  quantumIsingDisagreementSet sigma tau = quantumIsingDisagreementSet tau sigma := by
-- proof
  apply StatMech.FrontierA.quantumIsingDisagreementSet_comm sigma tau

/--
[quantumIsingDisagreementCount_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingDisagreementCount_comm_eq
  {L : Nat}
  {sigma tau : QuantumIsingChainConfig L} :
-- imply
  quantumIsingDisagreementCount sigma tau = quantumIsingDisagreementCount tau sigma := by
-- proof
  apply StatMech.FrontierA.quantumIsingDisagreementCount_comm sigma tau

/--
[quantumIsingDisagreementCount_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingDisagreementCount_self_eq
  {L : Nat}
  {sigma : QuantumIsingChainConfig L} :
-- imply
  quantumIsingDisagreementCount sigma sigma = 0 := by
-- proof
  apply StatMech.FrontierA.quantumIsingDisagreementCount_self sigma

/--
[quantumIsingDisagreementCount_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingDisagreementCount_eq_zero_iff_eq
  {L : Nat}
  {sigma tau : QuantumIsingChainConfig L} :
-- imply
  quantumIsingDisagreementCount sigma tau = 0 ↔ sigma = tau := by
-- proof
  apply StatMech.FrontierA.quantumIsingDisagreementCount_eq_zero_iff sigma tau

/--
[quantumIsingHamiltonian_apply_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingHamiltonian_apply_diag_eq
  {L : Nat}
  {sigma : QuantumIsingChainConfig L}
-- given
  (h : Real) :
-- imply
  quantumIsingHamiltonian h L sigma sigma = -(quantumIsingChainInteraction L sigma : Complex) / 4 := by
-- proof
  apply StatMech.FrontierA.quantumIsingHamiltonian_apply_diag h L sigma

/--
[quantumIsingHamiltonian_apply_oneFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingHamiltonian_apply_oneFlip_eq
  {L : Nat}
  {sigma tau : QuantumIsingChainConfig L}
-- given
  (h : Real)
  (hne : sigma ≠ tau)
  (hflip : quantumIsingDisagreementCount sigma tau = 1) :
-- imply
  quantumIsingHamiltonian h L sigma tau = -(h : Complex) / 2 := by
-- proof
  apply StatMech.FrontierA.quantumIsingHamiltonian_apply_oneFlip h L sigma tau hne hflip

/--
[quantumIsingHamiltonian_apply_other](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingHamiltonian_apply_other_eq
  {L : Nat}
  {sigma tau : QuantumIsingChainConfig L}
-- given
  (h : Real)
  (hne : sigma ≠ tau)
  (hflip : quantumIsingDisagreementCount sigma tau ≠ 1) :
-- imply
  quantumIsingHamiltonian h L sigma tau = 0 := by
-- proof
  apply StatMech.FrontierA.quantumIsingHamiltonian_apply_other h L sigma tau hne hflip

/--
[quantumIsingHamiltonian_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingHamiltonian_isHermitian_eq
  {L : Nat}
-- given
  (h : Real) :
-- imply
  (quantumIsingHamiltonian h L).IsHermitian := by
-- proof
  apply StatMech.FrontierA.quantumIsingHamiltonian_isHermitian h L

/--
[quantumIsingBoltzmannGenerator_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingBoltzmannGenerator_apply_eq
  {L : Nat}
  {sigma tau : QuantumIsingChainConfig L}
-- given
  (beta h : Real) :
-- imply
  quantumIsingBoltzmannGenerator beta h L sigma tau = if sigma = tau then (beta / 4 * quantumIsingChainInteraction L sigma : Real) else if quantumIsingDisagreementCount sigma tau = 1 then (beta * h / 2 : Real) else 0 := by
-- proof
  apply StatMech.FrontierA.quantumIsingBoltzmannGenerator_apply beta h L sigma tau

/--
[quantumIsingTrotterTransferKernel_eq_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingTrotterTransferKernel_eq_step_eq
  {n L : Nat}
  {sigma tau : QuantumIsingChainConfig L}
-- given
  (beta h : Real)
  (hn : n ≠ 0) :
-- imply
  (quantumIsingTrotterTransferKernel beta h n L sigma tau : Complex) = quantumIsingTrotterStep beta h L (1 / n) sigma tau := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterTransferKernel_eq_step beta h n L hn sigma tau

/--
[quantumIsingTrotterTransferMatrix_eq_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingTrotterTransferMatrix_eq_step_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0) :
-- imply
  quantumIsingTrotterTransferMatrix beta h n L = quantumIsingTrotterStep beta h L (1 / n) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterTransferMatrix_eq_step beta h n L hn

/--
[quantumIsingTrotterStep_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingTrotterStep_zero_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  quantumIsingTrotterStep beta h L 0 = 1 := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterStep_zero beta h L

/--
[quantumIsingTrotterStep_entry_hasDerivAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean)
-/
@[path]
private lemma quantumIsingTrotterStep_entry_hasDerivAt_zero_eq
  {L : Nat}
  {sigma tau : QuantumIsingChainConfig L}
-- given
  (beta h : Real) :
-- imply
  HasDerivAt (fun t => quantumIsingTrotterStep beta h L t sigma tau) (quantumIsingBoltzmannGenerator beta h L sigma tau) 0 := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterStep_entry_hasDerivAt_zero beta h L sigma tau


-- created on 2026-10-23
