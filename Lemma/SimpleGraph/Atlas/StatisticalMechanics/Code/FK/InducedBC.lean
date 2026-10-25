import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
open SimpleGraph StatMech StatMech.FK


/--
[psiExt_innerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma psiExt_innerEdge_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {e : Sym2 (boxVerts d n)} :
-- imply
  psiExt d n ψ ω (innerEdge d n e) = ω e := by
-- proof
  apply StatMech.FK.psiExt_innerEdge d n ψ ω e

/--
[psiExt_eq_psi_of_not_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma psiExt_eq_psi_of_not_range_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {e : Sym2 (boxVerts d (n+1))}
-- given
  (he : e ∉ Set.range (innerEdge d n)) :
-- imply
  psiExt d n ψ ω e = ψ e := by
-- proof
  apply StatMech.FK.psiExt_eq_psi_of_not_range d n ψ ω he

/--
[psiExt_innerEdge_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma psiExt_innerEdge_pair_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n} :
-- imply
  psiExt d n ψ ω s(boxVertIncl d n x, boxVertIncl d n y) = ω s(x, y) := by
-- proof
  apply StatMech.FK.psiExt_innerEdge_pair d n ψ ω x y

/--
[innerRestrict_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma innerRestrict_psiExt_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  innerRestrict d n (psiExt d n ψ ω) = ω := by
-- proof
  apply StatMech.FK.innerRestrict_psiExt d n ψ ω

/--
[agreesOff_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma agreesOff_psiExt_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  AgreesOff (innerEdgeFinset d n) ψ (psiExt d n ψ ω) := by
-- proof
  apply StatMech.FK.agreesOff_psiExt d n ψ ω

/--
[psiExt_innerRestrict_of_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma psiExt_innerRestrict_of_agreesOff_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
-- given
  (hρ : AgreesOff (innerEdgeFinset d n) ψ ρ) :
-- imply
  psiExt d n ψ (innerRestrict d n ρ) = ρ := by
-- proof
  apply StatMech.FK.psiExt_innerRestrict_of_agreesOff d n hρ

/--
[condFibre_eq_image_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma condFibre_eq_image_psiExt_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  condFibre (innerEdgeFinset d n) ψ = Finset.univ.image (psiExt d n ψ) := by
-- proof
  apply StatMech.FK.condFibre_eq_image_psiExt d n ψ

/--
[outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma outsideGraph_adj_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d (n+1)} :
-- imply
  (outsideGraph d n ψ).Adj x y ↔ ((boxGraph d (n+1)).Adj x y ∧ ψ s(x, y) = true ∧ s(x, y) ∉ Set.range (innerEdge d n)) ∨ (x ≠ y ∧ boxBoundary d (n+1) x ∧ boxBoundary d (n+1) y) := by
-- proof
  apply StatMech.FK.outsideGraph_adj d n ψ x y

/--
[inducedWiring_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma inducedWiring_adj_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n} :
-- imply
  (inducedWiring d n ψ).Adj x y ↔ x ≠ y ∧ (outsideGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
-- proof
  apply StatMech.FK.inducedWiring_adj d n ψ x y

/--
[psiExt_eq_false_of_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma psiExt_eq_false_of_range_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {e : Sym2 (boxVerts d (n+1))}
-- given
  (he : e ∈ Set.range (innerEdge d n)) :
-- imply
  psiExt d n ψ ω e = psiExt d n (fun _ => false) ω e := by
-- proof
  apply StatMech.FK.psiExt_eq_false_of_range d n ψ ω he

/--
[psiWiredGraph_eq_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma psiWiredGraph_eq_sup_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  openSub (boxGraph d (n+1)) (psiExt d n ψ ω) ⊔ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1)) = innerImageGraph d n ω ⊔ outsideGraph d n ψ := by
-- proof
  apply StatMech.FK.psiWiredGraph_eq_sup d n ψ ω

/--
[outsideGraph_le_fullGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma outsideGraph_le_fullGraph_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  outsideGraph d n ψ ≤ fullGraph d n ω ψ := by
-- proof
  apply StatMech.FK.outsideGraph_le_fullGraph d n ω ψ

/--
[innerImageGraph_adj_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma innerImageGraph_adj_inner_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {u v : boxVerts d (n+1)}
-- given
  (h : (innerImageGraph d n ω).Adj u v) :
-- imply
  IsInnerVert d n u ∧ IsInnerVert d n v := by
-- proof
  apply StatMech.FK.innerImageGraph_adj_inner d n ω h

/--
[innerImageGraph_adj_boxVertIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma innerImageGraph_adj_boxVertIncl_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n} :
-- imply
  (innerImageGraph d n ω).Adj (boxVertIncl d n x) (boxVertIncl d n y) ↔ (openSub (boxGraph d n) ω).Adj x y := by
-- proof
  apply StatMech.FK.innerImageGraph_adj_boxVertIncl d n ω x y

/--
[innerGraph_reachable_of_outsideReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma innerGraph_reachable_of_outsideReachable_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n}
-- given
  (h : (outsideGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
-- imply
  (innerGraph d n ω ψ).Reachable x y := by
-- proof
  apply StatMech.FK.innerGraph_reachable_of_outsideReachable d n ω ψ h

/--
[fullGraph_reachable_of_innerGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma fullGraph_reachable_of_innerGraph_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n}
-- given
  (h : (innerGraph d n ω ψ).Reachable x y) :
-- imply
  (fullGraph d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
-- proof
  apply StatMech.FK.fullGraph_reachable_of_innerGraph d n ω ψ h

/--
[innerGraph_reachable_of_fullGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma innerGraph_reachable_of_fullGraph_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n}
-- given
  (h : (fullGraph d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
-- imply
  (innerGraph d n ω ψ).Reachable x y := by
-- proof
  apply StatMech.FK.innerGraph_reachable_of_fullGraph d n ω ψ h

/--
[fullGraph_reachable_boxVertIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma fullGraph_reachable_boxVertIncl_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n} :
-- imply
  (fullGraph d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) ↔ (innerGraph d n ω ψ).Reachable x y := by
-- proof
  apply StatMech.FK.fullGraph_reachable_boxVertIncl d n ω ψ x y

/--
[fullGraph_adj_of_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma fullGraph_adj_of_outside_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {u w : boxVerts d (n+1)}
-- given
  (hu : ¬ IsInnerVert d n u)
  (h : (fullGraph d n ω ψ).Adj u w) :
-- imply
  (outsideGraph d n ψ).Adj u w := by
-- proof
  apply StatMech.FK.fullGraph_adj_of_outside d n ω ψ hu h

/--
[outsideOnly_self_not_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma outsideOnly_self_not_inner_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {u : boxVerts d (n+1)}
-- given
  (hu : OutsideOnly d n ψ u) :
-- imply
  ¬ IsInnerVert d n u := by
-- proof
  apply StatMech.FK.outsideOnly_self_not_inner d n ψ hu

/--
[outsideOnly_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma outsideOnly_of_reachable_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {u v : boxVerts d (n+1)}
-- given
  (hu : OutsideOnly d n ψ u)
  (h : (outsideGraph d n ψ).Reachable u v) :
-- imply
  OutsideOnly d n ψ v := by
-- proof
  apply StatMech.FK.outsideOnly_of_reachable d n ψ hu h

/--
[outsideGraph_reachable_of_fullGraph_outsideOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma outsideGraph_reachable_of_fullGraph_outsideOnly_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {u w : boxVerts d (n+1)}
-- given
  (hu : OutsideOnly d n ψ u)
  (h : (fullGraph d n ω ψ).Reachable u w) :
-- imply
  (outsideGraph d n ψ).Reachable u w := by
-- proof
  apply StatMech.FK.outsideGraph_reachable_of_fullGraph_outsideOnly d n ω ψ hu h

/--
[isOutsideOnly_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma isOutsideOnly_mk_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {v : boxVerts d (n+1)} :
-- imply
  IsOutsideOnly d n ψ ((outsideGraph d n ψ).connectedComponentMk v) ↔ OutsideOnly d n ψ v := by
-- proof
  apply StatMech.FK.isOutsideOnly_mk d n ψ v

/--
[fullComponentMap_inl_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma fullComponentMap_inl_mk_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x : boxVerts d n} :
-- imply
  fullComponentMap d n ω ψ (Sum.inl ((innerGraph d n ω ψ).connectedComponentMk x)) = (fullGraph d n ω ψ).connectedComponentMk (boxVertIncl d n x) := by
-- proof
  apply StatMech.FK.fullComponentMap_inl_mk d n ω ψ x

/--
[fullComponentMap_inr_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma fullComponentMap_inr_mk_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {v : boxVerts d (n+1)}
-- given
  (hv : IsOutsideOnly d n ψ ((outsideGraph d n ψ).connectedComponentMk v)) :
-- imply
  fullComponentMap d n ω ψ (Sum.inr ⟨(outsideGraph d n ψ).connectedComponentMk v, hv⟩) = (fullGraph d n ω ψ).connectedComponentMk v := by
-- proof
  apply StatMech.FK.fullComponentMap_inr_mk d n ω ψ v hv

/--
[fullComponentMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma fullComponentMap_injective_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  Function.Injective (fullComponentMap d n ω ψ) := by
-- proof
  apply StatMech.FK.fullComponentMap_injective d n ω ψ

/--
[fullComponentMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma fullComponentMap_surjective_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  Function.Surjective (fullComponentMap d n ω ψ) := by
-- proof
  apply StatMech.FK.fullComponentMap_surjective d n ω ψ

/--
[numClustersBC_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma numClustersBC_psiExt_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  numClustersBC (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) (psiExt d n ψ ω) = numClustersBC (boxGraph d n) (inducedWiring d n ψ) ω + outsideShift d n ψ := by
-- proof
  apply StatMech.FK.numClustersBC_psiExt d n ω ψ

/--
[psiEdgeFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma psiEdgeFactor_pos_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < psiEdgeFactor d n ψ p := by
-- proof
  apply StatMech.FK.psiEdgeFactor_pos hp hp1

/--
[edgeProduct_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma edgeProduct_psiExt_eq
  {d : ℕ}
  {d n : ℕ}
  {p : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  edgeProduct (boxGraph d (n+1)) p (psiExt d n ψ ω) = edgeProduct (boxGraph d n) p ω * psiEdgeFactor d n ψ p := by
-- proof
  apply StatMech.FK.edgeProduct_psiExt d n ψ ω

/--
[psiShift_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma psiShift_pos_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < psiShift d n ψ p q := by
-- proof
  apply StatMech.FK.psiShift_pos hp hp1 hq

/--
[bcWeight_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma bcWeight_psiExt_eq
  {d : ℕ}
  {d n : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  bcWeight (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p q (psiExt d n ψ ω) = bcWeight (boxGraph d n) (inducedWiring d n ψ) p q ω * psiShift d n ψ p q := by
-- proof
  apply StatMech.FK.bcWeight_psiExt d n ψ ω

/--
[inducedBcZ_innerEdgeFinset_psi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma inducedBcZ_innerEdgeFinset_psi_eq
  {d : ℕ}
  {d n : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  inducedBcZ (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p q (innerEdgeFinset d n) ψ = bcZ (boxGraph d n) (inducedWiring d n ψ) p q * psiShift d n ψ p q := by
-- proof
  apply StatMech.FK.inducedBcZ_innerEdgeFinset_psi d n ψ

/--
[condBcProb_psiExt_eq_bcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma condBcProb_psiExt_eq_bcProb_eq
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
  condBcProb (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p q (innerEdgeFinset d n) ψ (psiExt d n ψ ω) = bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω := by
-- proof
  apply StatMech.FK.condBcProb_psiExt_eq_bcProb d n hp hp1 hq ψ ω

/--
[notMem_box_pred_of_adj_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma notMem_box_pred_of_adj_outer_eq
  {d : ℕ}
  {d n : ℕ}
  {x y : Site d}
-- given
  (hn : 1 ≤ n)
  (hx : x ∈ StatMech.Lattice.box d n)
  (hadj : StatMech.Lattice.NearestNeighbour d x y)
  (hy : y ∉ StatMech.Lattice.box d n) :
-- imply
  x ∉ StatMech.Lattice.box d (n - 1) := by
-- proof
  apply StatMech.FK.notMem_box_pred_of_adj_outer hn hx hadj hy

/--
[boxBoundary_of_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma boxBoundary_of_outsideGraph_adj_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x : boxVerts d n}
  {z : boxVerts d (n+1)}
-- given
  (hn : 1 ≤ n)
  (h : (outsideGraph d n ψ).Adj (boxVertIncl d n x) z) :
-- imply
  boxBoundary d n x := by
-- proof
  apply StatMech.FK.boxBoundary_of_outsideGraph_adj d n hn ψ h

/--
[inducedWiring_only_bdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma inducedWiring_only_bdry_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {x y : boxVerts d n}
-- given
  (h : (inducedWiring d n ψ).Adj x y) :
-- imply
  boxBoundary d n x ∧ boxBoundary d n y := by
-- proof
  apply StatMech.FK.inducedWiring_only_bdry d n ψ h

/--
[inducedWiring_le_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma inducedWiring_le_wired_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  inducedWiring d n ψ ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n) := by
-- proof
  apply StatMech.FK.inducedWiring_le_wired d n ψ

/--
[condBcProb_psiExt_sum_eq_inducedBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma condBcProb_psiExt_sum_eq_inducedBox_eq
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
  (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p q (innerEdgeFinset d n) ψ ρ) = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω * bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω := by
-- proof
  apply StatMech.FK.condBcProb_psiExt_sum_eq_inducedBox d n hp hp1 hq ψ B

/--
[condBcProb_psiExt_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma condBcProb_psiExt_dominated_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1:ℝ)) ω * bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω) ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * bcProb (boxGraph d n) (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n)) p q ω := by
-- proof
  apply StatMech.FK.condBcProb_psiExt_dominated d n ψ hp hp1 hq hA

/--
[condBcProb_psiExt_dominated_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean)
-/
@[path]
private lemma condBcProb_psiExt_dominated_wired_eq
  {d : ℕ}
  {d n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1:ℝ)) ω * bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω) ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.condBcProb_psiExt_dominated_wired d n ψ hp hp1 hq hA


-- created on 2026-10-23
