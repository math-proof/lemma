import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
open Finset StatMech StatMech.Ising


/--
[spin_isingSumConfigEquiv_symm_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma spin_isingSumConfigEquiv_symm_inl_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {s : ConfigSpace V}
  {t : ConfigSpace W}
  {x : V} :
-- imply
  spin (isingSumConfigEquiv.symm (s, t)) (Sum.inl x) = spin s x := by
-- proof
  apply StatMech.Ising.spin_isingSumConfigEquiv_symm_inl s t x

/--
[spin_isingSumConfigEquiv_symm_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma spin_isingSumConfigEquiv_symm_inr_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {s : ConfigSpace V}
  {t : ConfigSpace W}
  {x : W} :
-- imply
  spin (isingSumConfigEquiv.symm (s, t)) (Sum.inr x) = spin t x := by
-- proof
  apply StatMech.Ising.spin_isingSumConfigEquiv_symm_inr s t x

/--
[spinProd_isingSumConfigEquiv_symm_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma spinProd_isingSumConfigEquiv_symm_inl_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {s : ConfigSpace V}
  {t : ConfigSpace W}
  {A : Finset V} :
-- imply
  spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩) (isingSumConfigEquiv.symm (s, t)) = spinProd A s := by
-- proof
  apply StatMech.Ising.spinProd_isingSumConfigEquiv_symm_inl s t A

/--
[bond_isingSumConfigEquiv_symm_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma bond_isingSumConfigEquiv_symm_inl_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {s : ConfigSpace V}
  {t : ConfigSpace W}
  {e : Sym2 V} :
-- imply
  bond (isingSumConfigEquiv.symm (s, t)) (Sym2.map Sum.inl e) = bond s e := by
-- proof
  apply StatMech.Ising.bond_isingSumConfigEquiv_symm_inl s t e

/--
[bond_isingSumConfigEquiv_symm_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma bond_isingSumConfigEquiv_symm_inr_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {s : ConfigSpace V}
  {t : ConfigSpace W}
  {e : Sym2 W} :
-- imply
  bond (isingSumConfigEquiv.symm (s, t)) (Sym2.map Sum.inr e) = bond t e := by
-- proof
  apply StatMech.Ising.bond_isingSumConfigEquiv_symm_inr s t e

/--
[sum_bond_isingSumConfigEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma sum_bond_isingSumConfigEquiv_symm_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {s : ConfigSpace V}
  {t : ConfigSpace W} :
-- imply
  (∑ e ∈ (G ⊕g H).edgeFinset, bond (isingSumConfigEquiv.symm (s, t)) e) = (∑ e ∈ G.edgeFinset, bond s e) + ∑ e ∈ H.edgeFinset, bond t e := by
-- proof
  apply StatMech.Ising.sum_bond_isingSumConfigEquiv_symm G H s t

/--
[hamiltonian_isingSumConfigEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma hamiltonian_isingSumConfigEquiv_symm_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {s : ConfigSpace V}
  {t : ConfigSpace W}
-- given
  (h : ℝ) :
-- imply
  hamiltonian (G ⊕g H) h (isingSumConfigEquiv.symm (s, t)) = hamiltonian G h s + hamiltonian H h t := by
-- proof
  apply StatMech.Ising.hamiltonian_isingSumConfigEquiv_symm G H h s t

/--
[isingWeight_isingSumConfigEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma isingWeight_isingSumConfigEquiv_symm_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {s : ConfigSpace V}
  {t : ConfigSpace W}
-- given
  (beta h : ℝ) :
-- imply
  isingWeight (G ⊕g H) beta h (isingSumConfigEquiv.symm (s, t)) = isingWeight G beta h s * isingWeight H beta h t := by
-- proof
  apply StatMech.Ising.isingWeight_isingSumConfigEquiv_symm G H beta h s t

/--
[isingZ_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma isingZ_sum_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
-- given
  (beta h : ℝ) :
-- imply
  isingZ (G ⊕g H) beta h = isingZ G beta h * isingZ H beta h := by
-- proof
  apply StatMech.Ising.isingZ_sum G H beta h

/--
[isingProb_isingSumConfigEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma isingProb_isingSumConfigEquiv_symm_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {s : ConfigSpace V}
  {t : ConfigSpace W}
-- given
  (beta h : ℝ) :
-- imply
  isingProb (G ⊕g H) beta h (isingSumConfigEquiv.symm (s, t)) = isingProb G beta h s * isingProb H beta h t := by
-- proof
  apply StatMech.Ising.isingProb_isingSumConfigEquiv_symm G H beta h s t

/--
[isingExpectation_spin_sum_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma isingExpectation_spin_sum_inl_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {x : V}
-- given
  (beta h : ℝ) :
-- imply
  isingExpectation (G ⊕g H) beta h (fun s => spin s (Sum.inl x)) = isingExpectation G beta h (fun s => spin s x) := by
-- proof
  apply StatMech.Ising.isingExpectation_spin_sum_inl G H beta h x

/--
[isingExpectation_spinProd_sum_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean)
-/
@[path]
private lemma isingExpectation_spinProd_sum_inl_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {A : Finset V}
-- given
  (beta h : ℝ) :
-- imply
  isingExpectation (G ⊕g H) beta h (spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) = isingExpectation G beta h (spinProd A) := by
-- proof
  apply StatMech.Ising.isingExpectation_spinProd_sum_inl G H beta h A


-- created on 2026-10-23
