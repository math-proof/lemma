import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs
open Set StatMech.Lattice SimpleGraph StatMech StatMech.BeffaraDC StatMech.BeffaraDC.SymmetricDomain


/--
[mem_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma mem_annulus_eq
  {n N : ℕ}
  {x : Site 2} :
-- imply
  x ∈ annulus n N ↔ x ∈ box 2 N ∧ x ∉ box 2 n := by
-- proof
  apply StatMech.BeffaraDC.mem_annulus

/--
[annulus_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma annulus_subset_box_eq
  {n N : ℕ} :
-- imply
  annulus n N ⊆ box 2 N := by
-- proof
  apply StatMech.BeffaraDC.annulus_subset_box n N

/--
[annulus_disjoint_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma annulus_disjoint_inner_eq
  {n N : ℕ} :
-- imply
  Disjoint (annulus n N) (box 2 n) := by
-- proof
  apply StatMech.BeffaraDC.annulus_disjoint_inner n N

/--
[annulus_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma annulus_finite_eq
  {n N : ℕ} :
-- imply
  (annulus n N).Finite := by
-- proof
  apply StatMech.BeffaraDC.annulus_finite n N

/--
[annulus_empty_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma annulus_empty_of_le_eq
  {N : ℕ} :
-- imply
  annulus N N = ∅ := by
-- proof
  apply StatMech.BeffaraDC.annulus_empty_of_le N

/--
[openSubgraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma openSubgraph_mono_eq
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ω ≤ ω') :
-- imply
  openSubgraph 2 ω ≤ openSubgraph 2 ω' := by
-- proof
  apply StatMech.BeffaraDC.openSubgraph_mono h

/--
[IsAnnulusCircuit.isCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma isCircuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n N : ℕ}
  {x : Site 2}
  {w : (openSubgraph 2 ω).Walk x x}
-- given
  (h : IsAnnulusCircuit ω n N w) :
-- imply
  w.IsCircuit := by
-- proof
  apply StatMech.BeffaraDC.IsAnnulusCircuit.isCircuit h

/--
[IsAnnulusCircuit.support_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma support_subset_box_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n N : ℕ}
  {x : Site 2}
  {w : (openSubgraph 2 ω).Walk x x}
-- given
  (h : IsAnnulusCircuit ω n N w) :
-- imply
  ∀ y ∈ w.support, y ∈ box 2 N := by
-- proof
  apply StatMech.BeffaraDC.IsAnnulusCircuit.support_subset_box h

/--
[IsAnnulusCircuit.support_avoids_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma support_avoids_inner_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n N : ℕ}
  {x : Site 2}
  {w : (openSubgraph 2 ω).Walk x x}
-- given
  (h : IsAnnulusCircuit ω n N w) :
-- imply
  ∀ y ∈ w.support, y ∉ box 2 n := by
-- proof
  apply StatMech.BeffaraDC.IsAnnulusCircuit.support_avoids_inner h

/--
[IsAnnulusCircuit.base_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma base_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n N : ℕ}
  {x : Site 2}
  {w : (openSubgraph 2 ω).Walk x x}
-- given
  (h : IsAnnulusCircuit ω n N w) :
-- imply
  x ∈ annulus n N := by
-- proof
  apply StatMech.BeffaraDC.IsAnnulusCircuit.base_mem h

/--
[Separates.mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma mono_eq
  {C C' : Set (Site 2)}
  {n N : ℕ}
-- given
  (hCC' : C ⊆ C')
  (h : Separates C n N) :
-- imply
  Separates C' n N := by
-- proof
  apply StatMech.BeffaraDC.Separates.mono hCC' h

/--
[mem_annulusEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma mem_annulusEvent_eq
  {n N M : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ annulusEvent n N M ↔ AnnulusEvent ω n N M := by
-- proof
  apply StatMech.BeffaraDC.mem_annulusEvent

/--
[mapLe_isCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma mapLe_isCircuit_eq
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2}
  {w : (openSubgraph 2 ω).Walk x x}
-- given
  (h : ω ≤ ω')
  (hc : w.IsCircuit) :
-- imply
  (w.mapLe (openSubgraph_mono h)).IsCircuit := by
-- proof
  apply StatMech.BeffaraDC.mapLe_isCircuit h hc

/--
[mapLe_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma mapLe_support_eq
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2}
  {w : (openSubgraph 2 ω).Walk x x}
-- given
  (h : ω ≤ ω') :
-- imply
  (w.mapLe (openSubgraph_mono h)).support = w.support := by
-- proof
  apply StatMech.BeffaraDC.mapLe_support h w

/--
[IsAnnulusCircuit.mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma mono_eq_2
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
  {n N : ℕ}
  {x : Site 2}
  {w : (openSubgraph 2 ω).Walk x x}
-- given
  (h : ω ≤ ω')
  (hw : IsAnnulusCircuit ω n N w) :
-- imply
  IsAnnulusCircuit ω' n N (w.mapLe (openSubgraph_mono h)) := by
-- proof
  apply StatMech.BeffaraDC.IsAnnulusCircuit.mono h hw

/--
[annulusEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma annulusEvent_increasing_eq
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
  {n N M : ℕ}
-- given
  (h : ω ≤ ω')
  (hω : ω ∈ annulusEvent n N M) :
-- imply
  ω' ∈ annulusEvent n N M := by
-- proof
  apply StatMech.BeffaraDC.annulusEvent_increasing h hω

/--
[diagReflFun_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma diagReflFun_apply_eq
  {a b : ℤ} :
-- imply
  diagReflFun ![a, b] = ![b, a] := by
-- proof
  apply StatMech.BeffaraDC.diagReflFun_apply a b

/--
[diagReflFun_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma diagReflFun_involutive_eq :
-- imply
  Function.Involutive diagReflFun := by
-- proof
  apply StatMech.BeffaraDC.diagReflFun_involutive

/--
[diagReflEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma diagReflEquiv_apply_eq
  {x : Site 2} :
-- imply
  diagReflEquiv x = diagReflFun x := by
-- proof
  apply StatMech.BeffaraDC.diagReflEquiv_apply x

/--
[diagReflEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma diagReflEquiv_symm_apply_eq
  {x : Site 2} :
-- imply
  diagReflEquiv.symm x = diagReflFun x := by
-- proof
  apply StatMech.BeffaraDC.diagReflEquiv_symm_apply x

/--
[diagRefl_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma diagRefl_adj_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj (diagReflFun x) (diagReflFun y) ↔ (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.BeffaraDC.diagRefl_adj x y

/--
[diagReflIso_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma diagReflIso_apply_eq
  {x : Site 2} :
-- imply
  diagReflIso x = diagReflFun x := by
-- proof
  apply StatMech.BeffaraDC.diagReflIso_apply x

/--
[IsSymmetricPair.symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma symm_eq
  {u₁ v₁ u₂ v₂ : Site 2}
  {γ₁ : LatticePath u₁ v₁}
  {γ₂ : LatticePath u₂ v₂}
-- given
  (h : IsSymmetricPair γ₁ γ₂) :
-- imply
  diagReflFun '' {z | z ∈ γ₂.support} = {z | z ∈ γ₁.support} := by
-- proof
  apply StatMech.BeffaraDC.IsSymmetricPair.symm h

/--
[wired_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma wired_subset_eq
  {D : SymmetricDomain} :
-- imply
  D.wired ⊆ D.G := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.wired_subset D

/--
[free_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma free_subset_eq
  {D : SymmetricDomain} :
-- imply
  D.free ⊆ D.G := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.free_subset D

/--
[wired_union_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma wired_union_free_eq
  {D : SymmetricDomain} :
-- imply
  D.wired ∪ D.free = D.G := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.wired_union_free D

/--
[wired_disjoint_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma wired_disjoint_free_eq
  {D : SymmetricDomain} :
-- imply
  Disjoint D.wired D.free := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.wired_disjoint_free D

/--
[wired_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma wired_finite_eq
  {D : SymmetricDomain} :
-- imply
  D.wired.Finite := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.wired_finite D

/--
[wired_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma wired_symm_eq
  {D : SymmetricDomain} :
-- imply
  diagReflFun '' D.wired = D.wired := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.wired_symm D

/--
[mem_connectionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma mem_connectionEvent_eq
  {D : SymmetricDomain}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ D.connectionEvent ↔ D.Connected ω := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.mem_connectionEvent D

/--
[Connected.connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma connected_eq
  {D : SymmetricDomain}
  {D : SymmetricDomain}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : D.Connected ω) :
-- imply
  ∃ x y : Site 2, x ∈ {z | z ∈ D.γ₁.support} ∧ y ∈ {z | z ∈ D.γ₂.support} ∧ StatMech.Lattice.Connected 2 ω x y := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.Connected.connected D h

/--
[connectionEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean)
-/
@[path]
private lemma connectionEvent_increasing_eq
  {D : SymmetricDomain}
  {D : SymmetricDomain}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ω ≤ ω')
  (hω : ω ∈ D.connectionEvent) :
-- imply
  ω' ∈ D.connectionEvent := by
-- proof
  apply StatMech.BeffaraDC.SymmetricDomain.connectionEvent_increasing D h hω


-- created on 2026-10-23
