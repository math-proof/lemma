import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
open MeasureTheory Filter Topology SimpleGraph StatMech StatMech.FK


/--
[inducedWiringFree_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma inducedWiringFree_adj_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n} :
-- imply
  (inducedWiringFree d n ψ).Adj x y ↔ x ≠ y ∧ (outsideOpenGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
-- proof
  apply StatMech.FK.inducedWiringFree_adj d n ψ x y

/--
[psiFreeGraph_eq_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma psiFreeGraph_eq_sup_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  openSub (boxGraph d (n+1)) (psiExt d n ψ ω) = innerImageGraph d n ω ⊔ outsideOpenGraph d n ψ := by
-- proof
  apply StatMech.FK.psiFreeGraph_eq_sup d n ψ ω

/--
[outsideOpenGraph_le_fullGraphFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma outsideOpenGraph_le_fullGraphFree_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  outsideOpenGraph d n ψ ≤ fullGraphFree d n ω ψ := by
-- proof
  apply StatMech.FK.outsideOpenGraph_le_fullGraphFree d n ω ψ

/--
[innerGraphFree_reachable_of_outsideReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma innerGraphFree_reachable_of_outsideReachable_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n}
-- given
  (h : (outsideOpenGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
-- imply
  (innerGraphFree d n ω ψ).Reachable x y := by
-- proof
  apply StatMech.FK.innerGraphFree_reachable_of_outsideReachable d n ω ψ h

/--
[fullGraphFree_reachable_of_innerGraphFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fullGraphFree_reachable_of_innerGraphFree_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n}
-- given
  (h : (innerGraphFree d n ω ψ).Reachable x y) :
-- imply
  (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
-- proof
  apply StatMech.FK.fullGraphFree_reachable_of_innerGraphFree d n ω ψ h

/--
[innerGraphFree_reachable_of_fullGraphFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma innerGraphFree_reachable_of_fullGraphFree_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n}
-- given
  (h : (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
-- imply
  (innerGraphFree d n ω ψ).Reachable x y := by
-- proof
  apply StatMech.FK.innerGraphFree_reachable_of_fullGraphFree d n ω ψ h

/--
[fullGraphFree_adj_of_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fullGraphFree_adj_of_outside_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {u w : boxVerts d (n+1)}
-- given
  (hu : ¬ IsInnerVert d n u)
  (h : (fullGraphFree d n ω ψ).Adj u w) :
-- imply
  (outsideOpenGraph d n ψ).Adj u w := by
-- proof
  apply StatMech.FK.fullGraphFree_adj_of_outside d n ω ψ hu h

/--
[outsideOnlyFree_self_not_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma outsideOnlyFree_self_not_inner_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {u : boxVerts d (n+1)}
-- given
  (hu : OutsideOnlyFree d n ψ u) :
-- imply
  ¬ IsInnerVert d n u := by
-- proof
  apply StatMech.FK.outsideOnlyFree_self_not_inner d n ψ hu

/--
[outsideOnlyFree_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma outsideOnlyFree_of_reachable_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {u v : boxVerts d (n+1)}
-- given
  (hu : OutsideOnlyFree d n ψ u)
  (h : (outsideOpenGraph d n ψ).Reachable u v) :
-- imply
  OutsideOnlyFree d n ψ v := by
-- proof
  apply StatMech.FK.outsideOnlyFree_of_reachable d n ψ hu h

/--
[outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {u w : boxVerts d (n+1)}
-- given
  (hu : OutsideOnlyFree d n ψ u)
  (h : (fullGraphFree d n ω ψ).Reachable u w) :
-- imply
  (outsideOpenGraph d n ψ).Reachable u w := by
-- proof
  apply StatMech.FK.outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly d n ω ψ hu h

/--
[isOutsideOnlyFree_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma isOutsideOnlyFree_mk_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {v : boxVerts d (n+1)} :
-- imply
  IsOutsideOnlyFree d n ψ ((outsideOpenGraph d n ψ).connectedComponentMk v) ↔ OutsideOnlyFree d n ψ v := by
-- proof
  apply StatMech.FK.isOutsideOnlyFree_mk d n ψ v

/--
[fullComponentMapFree_inl_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fullComponentMapFree_inl_mk_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x : boxVerts d n} :
-- imply
  fullComponentMapFree d n ω ψ (Sum.inl ((innerGraphFree d n ω ψ).connectedComponentMk x)) = (fullGraphFree d n ω ψ).connectedComponentMk (boxVertIncl d n x) := by
-- proof
  apply StatMech.FK.fullComponentMapFree_inl_mk d n ω ψ x

/--
[fullComponentMapFree_inr_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fullComponentMapFree_inr_mk_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {v : boxVerts d (n+1)}
-- given
  (hv : IsOutsideOnlyFree d n ψ ((outsideOpenGraph d n ψ).connectedComponentMk v)) :
-- imply
  fullComponentMapFree d n ω ψ (Sum.inr ⟨(outsideOpenGraph d n ψ).connectedComponentMk v, hv⟩) = (fullGraphFree d n ω ψ).connectedComponentMk v := by
-- proof
  apply StatMech.FK.fullComponentMapFree_inr_mk d n ω ψ v hv

/--
[fullComponentMapFree_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fullComponentMapFree_injective_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  Function.Injective (fullComponentMapFree d n ω ψ) := by
-- proof
  apply StatMech.FK.fullComponentMapFree_injective d n ω ψ

/--
[fullComponentMapFree_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fullComponentMapFree_surjective_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  Function.Surjective (fullComponentMapFree d n ω ψ) := by
-- proof
  apply StatMech.FK.fullComponentMapFree_surjective d n ω ψ

/--
[numClusters_psiExt_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma numClusters_psiExt_free_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  numClusters (boxGraph d (n+1)) (psiExt d n ψ ω) = numClustersBC (boxGraph d n) (inducedWiringFree d n ψ) ω + outsideShiftFree d n ψ := by
-- proof
  apply StatMech.FK.numClusters_psiExt_free d n ω ψ

/--
[psiShiftFree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma psiShiftFree_pos_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < psiShiftFree d n ψ p q := by
-- proof
  apply StatMech.FK.psiShiftFree_pos hp hp1 hq

/--
[fkWeight_psiExt_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkWeight_psiExt_free_eq
  {d : ℕ}
  {d n : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  fkWeight (boxGraph d (n+1)) p q (psiExt d n ψ ω) = bcWeight (boxGraph d n) (inducedWiringFree d n ψ) p q ω * psiShiftFree d n ψ p q := by
-- proof
  apply StatMech.FK.fkWeight_psiExt_free d n ψ ω

/--
[inducedFkZ_innerEdgeFinset_psi_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma inducedFkZ_innerEdgeFinset_psi_free_eq
  {d : ℕ}
  {d n : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  inducedFkZ (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ = bcZ (boxGraph d n) (inducedWiringFree d n ψ) p q * psiShiftFree d n ψ p q := by
-- proof
  apply StatMech.FK.inducedFkZ_innerEdgeFinset_psi_free d n ψ

/--
[condFkProb_psiExt_eq_bcProb_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma condFkProb_psiExt_eq_bcProb_free_eq
  {d : ℕ}
  {d n : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ (psiExt d n ψ ω) = bcProb (boxGraph d n) (inducedWiringFree d n ψ) p q ω := by
-- proof
  apply StatMech.FK.condFkProb_psiExt_eq_bcProb_free d n hp hp1 hq ψ ω

/--
[sum_fibreMass_eq_one_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma sum_fibreMass_eq_one_free_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ), (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, fkProb (boxGraph d (n+1)) p q σ) = 1 := by
-- proof
  apply StatMech.FK.sum_fibreMass_eq_one_free n hp hp1 hq

/--
[fkProb_eq_fibreMass_mul_condFkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkProb_eq_fibreMass_mul_condFkProb_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 (boxVerts d (n+1)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkProb (boxGraph d (n+1)) p q ω = (∑ ρ ∈ condFibre (innerEdgeFinset d n) ω, fkProb (boxGraph d (n+1)) p q ρ) * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ω ω := by
-- proof
  apply StatMech.FK.fkProb_eq_fibreMass_mul_condFkProb n hp hp1 hq ω

/--
[condFkProb_congr_dom_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma condFkProb_congr_dom_free_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {ψ ψ' ω : ConfigSpace (Sym2 (boxVerts d (n+1)))}
-- given
  (h : AgreesOff (innerEdgeFinset d n) ψ ψ') :
-- imply
  condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ω = condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ' ω := by
-- proof
  apply StatMech.FK.condFkProb_congr_dom_free n ψ ψ' ω h

/--
[freeSucc_fkProb_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma freeSucc_fkProb_decompose_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * fkProb (boxGraph d (n+1)) p q ρ) = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ), (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, fkProb (boxGraph d (n+1)) p q σ) * (∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ, B.indicator (fun _ => (1:ℝ)) ρ * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ) := by
-- proof
  apply StatMech.FK.freeSucc_fkProb_decompose n hp hp1 hq B

/--
[condFkProb_psiExt_sum_eq_inducedBox_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma condFkProb_psiExt_sum_eq_inducedBox_free_eq
  {d : ℕ}
  {d n : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ, B.indicator (fun _ => (1:ℝ)) ρ * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ) = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω * bcProb (boxGraph d n) (inducedWiringFree d n ψ) p q ω := by
-- proof
  apply StatMech.FK.condFkProb_psiExt_sum_eq_inducedBox_free d n hp hp1 hq ψ B

/--
[fkProb_le_inducedFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkProb_le_inducedFree_eq
  {d : ℕ}
  {d n : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA₀ : IsIncreasing A₀) :
-- imply
  (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω) ≤ ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * bcProb (boxGraph d n) (inducedWiringFree d n ψ) p q ω := by
-- proof
  apply StatMech.FK.fkProb_le_inducedFree d n hp hp1 hq ψ hA₀

/--
[fkProb_le_condFkProb_innerRestrict_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkProb_le_condFkProb_innerRestrict_free_eq
  {d : ℕ}
  {d n : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA₀ : IsIncreasing A₀) :
-- imply
  (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω) ≤ ∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ := by
-- proof
  apply StatMech.FK.fkProb_le_condFkProb_innerRestrict_free d n hp hp1 hq ψ hA₀

/--
[freeSucc_fkProb_innerEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma freeSucc_fkProb_innerEvent_le_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA₀ : IsIncreasing A₀) :
-- imply
  (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω) ≤ ∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ * fkProb (boxGraph d (n+1)) p q ρ := by
-- proof
  apply StatMech.FK.freeSucc_fkProb_innerEvent_le n hp hp1 hq hA₀

/--
[freeFiniteMeasure_real_boxRestrictEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_boxRestrictEvent_eq
  {d : ℕ}
  {m : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
-- imply
  (freeFiniteMeasure d m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S) = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)), S.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d m) p q ω := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_real_boxRestrictEvent m hp hp1 hq S hmeas

/--
[freeFiniteMeasure_succ_real_innerRestrictEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma freeFiniteMeasure_succ_real_innerRestrictEvent_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
-- imply
  (freeFiniteMeasure d (n+1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n+1))), (innerRestrict d n ⁻¹' S).indicator (fun _ => (1:ℝ)) ρ * fkProb (boxGraph d (n+1)) p q ρ := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_succ_real_innerRestrictEvent n hp hp1 hq S hmeas

/--
[freeFiniteMeasure_smallerBox_le_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma freeFiniteMeasure_smallerBox_le_succ_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S)
  (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
-- imply
  (∑ ω, S.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p 2 ω) ≤ (freeFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_smallerBox_le_succ n hp hp1 hS hmeas

/--
[fkFreeLimit_isIncreasing_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkFreeLimit_isIncreasing_preimage_eq
  {d : ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hS : IsIncreasing S) :
-- imply
  IsIncreasing (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkFreeLimit_isIncreasing_preimage N hS

/--
[fkFreeLimit_isClopen_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkFreeLimit_isClopen_preimage_eq
  {d : ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} :
-- imply
  IsClopen (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkFreeLimit_isClopen_preimage N S

/--
[fkFreeLimit_measurableSet_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkFreeLimit_measurableSet_preimage_eq
  {d : ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} :
-- imply
  MeasurableSet (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkFreeLimit_measurableSet_preimage N S

/--
[fkFreeLimit_le_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkFreeLimit_le_succ_eq
  {d : ℕ}
  {N m : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (freeFiniteMeasure d (m+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkFreeLimit_le_succ N m hNm hp hp1 hS

/--
[fkFreeLimit_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkFreeLimit_monotone_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  Monotone (fun k => (freeFiniteMeasure d (N+k) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) := by
-- proof
  apply StatMech.FK.fkFreeLimit_monotone N hp hp1 hS

/--
[freeFiniteMeasure_real_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_le_one_eq
  {d : ℕ}
  {m : ℕ}
  {p : ℝ}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real A ≤ 1 := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_real_le_one m hp hp1 A

/--
[fk_free_limit_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fk_free_limit_exists_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 (fkFreeLimitValue N hp hp1 S)) := by
-- proof
  apply StatMech.FK.fk_free_limit_exists N hp hp1 hS

/--
[fk_free_le_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fk_free_le_limit_eq
  {d : ℕ}
  {N m : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ fkFreeLimitValue N hp hp1 S := by
-- proof
  apply StatMech.FK.fk_free_le_limit N m hNm hp hp1 S

/--
[fkFreeLimit_freeInfiniteVolume_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fkFreeLimit_freeInfiniteVolume_eq_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) = fkFreeLimitValue N hp hp1 S := by
-- proof
  apply StatMech.FK.fkFreeLimit_freeInfiniteVolume_eq N hp hp1 hS

/--
[fk_free_infinite_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean)
-/
@[path]
private lemma fk_free_infinite_measure_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) := by
-- proof
  apply StatMech.FK.fk_free_infinite_measure N hp hp1 hS


-- created on 2026-10-23
