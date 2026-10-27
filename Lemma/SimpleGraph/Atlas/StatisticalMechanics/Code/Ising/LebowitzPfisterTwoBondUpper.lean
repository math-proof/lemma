import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBondUpper.Part2
open Set StatMech StatMech.Ising


/--
[twoBond_skew_ratio_le_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean)
-/
@[path]
private lemma twoBond_skew_ratio_le_product_eq
  {t a b e : Real}
-- given
  (ht0 : 0 <= t)
  (ht1 : t < 1)
  (ha0 : 0 <= a)
  (ha1 : a <= 1)
  (hb0 : 0 <= b)
  (hb1 : b <= 1)
  (he : a * b <= e) :
-- imply
  (1 + t * (a + b) + t ^ 2 * e) / (1 - t * (a + b) + t ^ 2 * e) <= ((1 + t * a) / (1 - t * a)) * ((1 + t * b) / (1 - t * b)) := by
-- proof
  apply StatMech.Ising.twoBond_skew_ratio_le_product ht0 ht1 ha0 ha1 hb0 hb1 he

/--
[twoBondInterfaceFreeEnergy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean)
-/
@[path]
private lemma twoBondInterfaceFreeEnergy_le_eq
  {K m1 m2 c : Real}
-- given
  (hK : 0 <= K)
  (hm10 : 0 <= m1)
  (hm11 : m1 <= 1)
  (hm20 : 0 <= m2)
  (hm21 : m2 <= 1)
  (hc0 : 0 <= c)
  (hc1 : c <= 1)
  (hgks : m1 * m2 <= c) :
-- imply
  twoBondInterfaceFreeEnergy K m1 m2 c <= 2 * K * (m1 ^ 2 + m2 ^ 2) := by
-- proof
  apply StatMech.Ising.twoBondInterfaceFreeEnergy_le hK hm10 hm11 hm20 hm21 hc0 hc1 hgks

/--
[twoReplicaTwoBridgeMoment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean)
-/
@[path]
private lemma twoReplicaTwoBridgeMoment_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  twoReplicaTwoBridgeMoment G J hf x y r = Real.cosh r ^ 2 + (Real.cosh r * Real.sinh r) * ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 + (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) + Real.sinh r ^ 2 * (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) ^ 2 := by
-- proof
  apply StatMech.Ising.twoReplicaTwoBridgeMoment_eq G J hf x y r

/--
[expJ_monomial_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean)
-/
@[path]
private lemma expJ_monomial_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (f : ConfigSpace V -> Real)
  (hfpm : forall s, f s <= 1) :
-- imply
  expJ E J hf f <= 1 := by
-- proof
  apply StatMech.Ising.expJ_monomial_le_one E J hf f hfpm

/--
[twoReplicaTwoBridgeFreeEnergy_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean)
-/
@[path]
private lemma twoReplicaTwoBridgeFreeEnergy_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {K : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  twoReplicaTwoBridgeFreeEnergy G J hf x y K = twoBondInterfaceFreeEnergy K (expJ G.edgeFinset J hf (fun s => spin s x)) (expJ G.edgeFinset J hf (fun s => spin s y)) (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) := by
-- proof
  apply StatMech.Ising.twoReplicaTwoBridgeFreeEnergy_eq G J hf x y K

/--
[twoReplicaTwoBridgeFreeEnergy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBondUpper.lean)
-/
@[path]
private lemma twoReplicaTwoBridgeFreeEnergy_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {K : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hK : 0 <= K) :
-- imply
  twoReplicaTwoBridgeFreeEnergy G J hf x y K <= 2 * K * ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 + (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) := by
-- proof
  apply StatMech.Ising.twoReplicaTwoBridgeFreeEnergy_le G J hf hJ hhf x y hxy K hK


-- created on 2026-10-23
