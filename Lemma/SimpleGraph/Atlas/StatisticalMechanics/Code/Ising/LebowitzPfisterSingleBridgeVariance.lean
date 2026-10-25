import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBridgeVariance.Part2
open StatMech StatMech.Ising


/--
[replicaBridgeInteraction_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeInteraction_unit_eq
  [Fintype V]
  [DecidableEq V]
  {x : V}
  {a b : ConfigSpace V} :
-- imply
  replicaBridgeInteraction (fun _ : Unit => x) a b = spin a x * spin b x := by
-- proof
  apply StatMech.Ising.replicaBridgeInteraction_unit x a b

/--
[replicaBridgeMoment_unit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeMoment_unit_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMoment G J hf (fun _ : Unit => x) r = Real.cosh r + (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 * Real.sinh r := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_unit_eq G J hf x r

/--
[replicaBridgeMean_unit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeMean_unit_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMean G J hf (fun _ : Unit => x) r = (Real.sinh r + (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 * Real.cosh r) / (Real.cosh r + (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 * Real.sinh r) := by
-- proof
  apply StatMech.Ising.replicaBridgeMean_unit_eq G J hf x r

/--
[replicaBridgeVariance_unit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeVariance_unit_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeVariance G J hf (fun _ : Unit => x) r = (1 - (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 4) / (Real.cosh r + (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 * Real.sinh r) ^ 2 := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_unit_eq G J hf x r

/--
[replicaBridgeVariance_unit_le_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeVariance_unit_le_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hr : 0 <= r) :
-- imply
  replicaBridgeVariance G J hf (fun _ : Unit => x) r <= replicaBridgeVariance G J hf (fun _ : Unit => x) (-r) := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_unit_le_neg G J hf hJ hhf x r hr

/--
[replicaCrossBridgeVariance_unit_same_le_negField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean)
-/
@[path]
private lemma replicaCrossBridgeVariance_unit_same_le_negField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hr : 0 <= r) :
-- imply
  replicaCrossBridgeVariance G J hf hf (fun _ : Unit => x) r <= replicaCrossBridgeVariance G J hf (fun v => -hf v) (fun _ : Unit => x) r := by
-- proof
  apply StatMech.Ising.replicaCrossBridgeVariance_unit_same_le_negField G J hf hJ hhf x r hr

/--
[replicaBridgeFreeEnergy_unit_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_unit_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hr : 0 <= r) :
-- imply
  replicaBridgeFreeEnergy G J hf (fun _ : Unit => x) r <= 2 * r * (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_unit_le G J hf hJ hhf x r hr

/--
[twoBridgeVarianceSkewPolynomial_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean)
-/
@[path]
private lemma twoBridgeVarianceSkewPolynomial_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {t A E : Real}
-- given
  (ht0 : 0 <= t)
  (ht1 : t <= 1)
  (hA0 : 0 <= A)
  (hE0 : 0 <= E)
  (hE1 : E <= 1)
  (hAE : A <= 1 + E) :
-- imply
  0 <= A ^ 2 * E * t ^ 4 - A ^ 2 - E ^ 3 * t ^ 4 - 3 * E ^ 2 * t ^ 4 + 2 * E ^ 2 * t ^ 2 - 2 * E * t ^ 2 + 3 * E + 1 := by
-- proof
  apply StatMech.Ising.twoBridgeVarianceSkewPolynomial_nonneg ht0 ht1 hA0 hE0 hE1 hAE

/--
[twoBridgeTiltVariance_le_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean)
-/
@[path]
private lemma twoBridgeTiltVariance_le_neg_eq
  [Fintype V]
  [DecidableEq V]
  {t A E : Real}
-- given
  (ht0 : 0 <= t)
  (ht1 : t < 1)
  (hA0 : 0 <= A)
  (hE0 : 0 <= E)
  (hE1 : E <= 1)
  (hAE : A <= 1 + E) :
-- imply
  twoBridgeTiltVariance t A E <= twoBridgeTiltVariance (-t) A E := by
-- proof
  apply StatMech.Ising.twoBridgeTiltVariance_le_neg ht0 ht1 hA0 hE0 hE1 hAE


-- created on 2026-10-23
