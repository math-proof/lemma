import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
open Finset StatMech StatMech.Ising


/--
[spin_eq_spinB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma spin_eq_spinB_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {x : V} :
-- imply
  spin s x = spinB (s x) := by
-- proof
  apply StatMech.Ising.spin_eq_spinB s x

/--
[monomial_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma monomial_zero_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  monomial (0 : V → ℕ) s = 1 := by
-- proof
  apply StatMech.Ising.monomial_zero s

/--
[monomial_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma monomial_add_eq
  [Fintype V]
  [DecidableEq V]
  {m₁ m₂ : V → ℕ}
  {s : ConfigSpace V} :
-- imply
  monomial (m₁ + m₂) s = monomial m₁ s * monomial m₂ s := by
-- proof
  apply StatMech.Ising.monomial_add m₁ m₂ s

/--
[sum_monomial_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma sum_monomial_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {m : V → ℕ} :
-- imply
  0 ≤ ∑ s : ConfigSpace V, monomial m s := by
-- proof
  apply StatMech.Ising.sum_monomial_nonneg m

/--
[IsSpinMonomial.const_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma const_one_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  IsSpinMonomial (fun _ : ConfigSpace V => (1 : ℝ)) := by
-- proof
  apply StatMech.Ising.IsSpinMonomial.const_one

/--
[IsSpinMonomial.mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma mul_eq
  [Fintype V]
  [DecidableEq V]
  {f g : ConfigSpace V → ℝ}
-- given
  (hf : IsSpinMonomial f)
  (hg : IsSpinMonomial g) :
-- imply
  IsSpinMonomial (fun s => f s * g s) := by
-- proof
  apply StatMech.Ising.IsSpinMonomial.mul hf hg

/--
[IsSpinMonomial.sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma sum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V → ℝ}
-- given
  (hf : IsSpinMonomial f) :
-- imply
  0 ≤ ∑ s : ConfigSpace V, f s := by
-- proof
  apply StatMech.Ising.IsSpinMonomial.sum_nonneg hf

/--
[isSpinMonomial_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma isSpinMonomial_spin_eq
  [Fintype V]
  [DecidableEq V]
  {x : V} :
-- imply
  IsSpinMonomial (fun s => spin s x) := by
-- proof
  apply StatMech.Ising.isSpinMonomial_spin x

/--
[isSpinMonomial_bond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma isSpinMonomial_bond_eq
  [Fintype V]
  [DecidableEq V]
  {e : Sym2 V} :
-- imply
  IsSpinMonomial (fun s => bond s e) := by
-- proof
  apply StatMech.Ising.isSpinMonomial_bond e

/--
[gks_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma gks_kernel_eq
  [Fintype V]
  [DecidableEq V]
  {I : Finset ι}
  {c d : ι → ℝ}
  {fac : ι → ConfigSpace V → ℝ}
  {obs : ConfigSpace V → ℝ}
-- given
  (hc : ∀ i ∈ I, 0 ≤ c i)
  (hd : ∀ i ∈ I, 0 ≤ d i)
  (hfac : ∀ i ∈ I, IsSpinMonomial (fac i))
  (hobs : IsSpinMonomial obs) :
-- imply
  0 ≤ ∑ s : ConfigSpace V, obs s * ∏ i ∈ I, (c i + d i * fac i s) := by
-- proof
  apply StatMech.Ising.gks_kernel I c d hc hd fac hfac obs hobs

/--
[spinProd_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma spinProd_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V} :
-- imply
  spinProd (∅ : Finset V) s = 1 := by
-- proof
  apply StatMech.Ising.spinProd_empty G s

/--
[isSpinMonomial_spinProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma isSpinMonomial_spinProd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V} :
-- imply
  IsSpinMonomial (spinProd A) := by
-- proof
  apply StatMech.Ising.isSpinMonomial_spinProd G A

/--
[bond_eq_pm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma bond_eq_pm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond s e = 1 ∨ bond s e = -1 := by
-- proof
  apply StatMech.Ising.bond_eq_pm G s e

/--
[spin_eq_pm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma spin_eq_pm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {x : V} :
-- imply
  spin s x = 1 ∨ spin s x = -1 := by
-- proof
  apply StatMech.Ising.spin_eq_pm G s x

/--
[exp_mul_pm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma exp_mul_pm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {c t : ℝ}
-- given
  (ht : t = 1 ∨ t = -1) :
-- imply
  Real.exp (c * t) = Real.cosh c + t * Real.sinh c := by
-- proof
  apply StatMech.Ising.exp_mul_pm G c t ht

/--
[isingWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma isingWeight_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  isingWeight G β h s = (∏ e ∈ G.edgeFinset, (Real.cosh β + bond s e * Real.sinh β)) * (∏ x : V, (Real.cosh (β * h) + spin s x * Real.sinh (β * h))) := by
-- proof
  apply StatMech.Ising.isingWeight_factor G β h s

/--
[sum_spinProd_isingWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma sum_spinProd_isingWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ ∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
-- proof
  apply StatMech.Ising.sum_spinProd_isingWeight_nonneg G β h hβ hh A

/--
[gks_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean)
-/
@[path]
private lemma gks_first_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation G β h (spinProd A) := by
-- proof
  apply StatMech.Ising.gks_first G β h hβ hh A


-- created on 2026-10-23
