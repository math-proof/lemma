import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi
open Filter Finset Set SimpleGraph Topology StatMech StatMech.Sharpness


/--
[abb_probV_eq_section](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_probV_eq_section_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → Real}
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hp0 : ∀ e, 0 ≤ p e)
  (hp1 : ∀ e, p e ≤ 1)
  (hA : StatMech.DependsOn A (F : Set E)) :
-- imply
  probV p A = probV (fun e : F ↦ p e) (ih_section A F) := by
-- proof
  apply StatMech.Sharpness.abb_probV_eq_section p hp0 hp1 A F hA

/--
[abb_probV_eq_of_agreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_probV_eq_of_agreeOn_eq
  [Fintype E]
  [DecidableEq E]
  {p q : E → Real}
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hp0 : ∀ e, 0 ≤ p e)
  (hp1 : ∀ e, p e ≤ 1)
  (hq0 : ∀ e, 0 ≤ q e)
  (hq1 : ∀ e, q e ≤ 1)
  (hA : StatMech.DependsOn A (F : Set E))
  (hpq : ∀ e ∈ F, p e = q e) :
-- imply
  probV p A = probV q A := by
-- proof
  apply StatMech.Sharpness.abb_probV_eq_of_agreeOn p q hp0 hp1 hq0 hq1 A F hA hpq

/--
[abb_internal_openSub_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_internal_openSub_adj_eq
  [DecidableEq W]
  {G : SimpleGraph W}
  {T : Finset W}
  {eta : ConfigSpace (abigInternalEdges T)}
  {a b : T} :
-- imply
  (openSub (G.induce (T : Set W)) (cfgEquiv (abigInternalEdgeEquiv T) eta)).Adj a b ↔ (openSub G (ih_fill (abigInternalEdges T) eta)).Adj (a : W) (b : W) := by
-- proof
  apply StatMech.Sharpness.abb_internal_openSub_adj G T eta a b

/--
[abb_preimage_connEvent_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_preimage_connEvent_induce_eq
  [DecidableEq W]
  {G : SimpleGraph W}
  {T : Finset W}
  {o x : T} :
-- imply
  (cfgEquiv (abigInternalEdgeEquiv T)) ⁻¹' connEvent (G.induce (T : Set W)) Set.univ o {x} = ih_section (connEvent G (T : Set W) (o : W) {(x : W)}) (abigInternalEdges T) := by
-- proof
  apply StatMech.Sharpness.abb_preimage_connEvent_induce G T o x

/--
[abb_probV_connEvent_eq_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_probV_connEvent_eq_induce_eq
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  {p : Sym2 W → Real}
  {T : Finset W}
  {o x : T}
-- given
  (hp0 : ∀ e, 0 ≤ p e)
  (hp1 : ∀ e, p e ≤ 1) :
-- imply
  probV p (connEvent G (T : Set W) (o : W) {(x : W)}) = probV (fun e : Sym2 T ↦ p (Sym2.map Subtype.val e)) (connEvent (G.induce (T : Set W)) Set.univ o {x}) := by
-- proof
  apply StatMech.Sharpness.abb_probV_connEvent_eq_induce G p hp0 hp1 T o x

/--
[abb_hom_real_eq_probV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_hom_real_eq_probV_eq
  [Fintype E]
  [DecidableEq E]
  {p : NNReal}
  {A : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1) :
-- imply
  (inhomBernoulliProductMeasure (fun _ : E ↦ p) (fun _ ↦ hp)).real A = probV (fun _ : E ↦ (p : Real)) A := by
-- proof
  apply StatMech.Sharpness.abb_hom_real_eq_probV p hp A

/--
[abb_probV_section_const_eq_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_probV_section_const_eq_induce_eq
  [DecidableEq W]
  {p : Real}
  {G : SimpleGraph W}
  {T : Finset W}
  {o x : T} :
-- imply
  probV (fun _ : abigInternalEdges T ↦ p) (ih_section (connEvent G (T : Set W) (o : W) {(x : W)}) (abigInternalEdges T)) = probV (fun _ : Sym2 T ↦ p) (connEvent (G.induce (T : Set W)) Set.univ o {x}) := by
-- proof
  apply StatMech.Sharpness.abb_probV_section_const_eq_induce p G T o x

/--
[abbEdgeEquiv_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbEdgeEquiv_mk_eq
  {sigma : V ≃ U}
  {x y : V} :
-- imply
  abbEdgeEquiv sigma s(x, y) = s(sigma x, sigma y) := by
-- proof
  apply StatMech.Sharpness.abbEdgeEquiv_mk sigma x y

/--
[abb_openSub_adj_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_openSub_adj_relabel_eq
  {G : SimpleGraph V}
  {H : SimpleGraph U}
  {sigma : V ≃ U}
  {omega : ConfigSpace (Sym2 U)}
  {x y : V}
-- given
  (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y)) :
-- imply
  (openSub G (cfgEquiv (abbEdgeEquiv sigma) omega)).Adj x y ↔ (openSub H omega).Adj (sigma x) (sigma y) := by
-- proof
  apply StatMech.Sharpness.abb_openSub_adj_relabel G H sigma hG omega x y

/--
[abb_connWithin_univ_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_connWithin_univ_relabel_eq
  {G : SimpleGraph V}
  {H : SimpleGraph U}
  {sigma : V ≃ U}
  {omega : ConfigSpace (Sym2 U)}
  {x y : V}
-- given
  (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y)) :
-- imply
  ConnWithin G (cfgEquiv (abbEdgeEquiv sigma) omega) Set.univ ⟨x, Set.mem_univ _⟩ ⟨y, Set.mem_univ _⟩ ↔ ConnWithin H omega Set.univ ⟨sigma x, Set.mem_univ _⟩ ⟨sigma y, Set.mem_univ _⟩ := by
-- proof
  apply StatMech.Sharpness.abb_connWithin_univ_relabel G H sigma hG omega x y

/--
[abb_preimage_connEvent_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_preimage_connEvent_relabel_eq
  {G : SimpleGraph V}
  {H : SimpleGraph U}
  {sigma : V ≃ U}
  {o x : V}
-- given
  (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y)) :
-- imply
  (cfgEquiv (abbEdgeEquiv sigma)) ⁻¹' connEvent G Set.univ o {x} = connEvent H Set.univ (sigma o) {sigma x} := by
-- proof
  apply StatMech.Sharpness.abb_preimage_connEvent_relabel G H sigma hG o x

/--
[abb_probV_connEvent_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_probV_connEvent_relabel_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype U]
  [DecidableEq U]
  {G : SimpleGraph V}
  {H : SimpleGraph U}
  {sigma : V ≃ U}
  {p : Sym2 V → Real}
  {o x : V}
-- given
  (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y)) :
-- imply
  probV p (connEvent G Set.univ o {x}) = probV (fun e : Sym2 U ↦ p ((abbEdgeEquiv sigma).symm e)) (connEvent H Set.univ (sigma o) {sigma x}) := by
-- proof
  apply StatMech.Sharpness.abb_probV_connEvent_relabel G H sigma hG p o x

/--
[abb_connEvent_univ_dependsOn_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_connEvent_univ_dependsOn_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {D : Finset (Sym2 V)}
  {o x : V}
-- given
  (hD : ∀ a b, G.Adj a b → s(a, b) ∈ D) :
-- imply
  StatMech.DependsOn (connEvent G Set.univ o {x}) (D : Set (Sym2 V)) := by
-- proof
  apply StatMech.Sharpness.abb_connEvent_univ_dependsOn_edges G D hD o x

/--
[mem_abbPhysicalSurface_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma mem_abbPhysicalSurface_iff_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {x : sctBox d n} :
-- imply
  x ∈ abbPhysicalSurface d n S ↔ some x ∈ S := by
-- proof
  apply StatMech.Sharpness.mem_abbPhysicalSurface_iff

/--
[mem_abbSiteSurface_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma mem_abbSiteSurface_iff_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {x : Site d} :
-- imply
  x ∈ abbSiteSurface d n S ↔ ∃ hx : x ∈ box d n, some (⟨x, hx⟩ : sctBox d n) ∈ S := by
-- proof
  apply StatMech.Sharpness.mem_abbSiteSurface_iff

/--
[abb_surface_eq_some_of_occurs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_surface_eq_some_of_occurs_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {z : Option (sctBox d n)}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (hz : z ∈ S) :
-- imply
  ∃ x, z = some x := by
-- proof
  apply StatMech.Sharpness.abb_surface_eq_some_of_occurs hocc hz

/--
[abbSurfaceValue_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbSurfaceValue_spec_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {z : S}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty) :
-- imply
  (z : Option (sctBox d n)) = some (abbSurfaceValue hocc z) := by
-- proof
  apply StatMech.Sharpness.abbSurfaceValue_spec hocc z

/--
[abbSurfaceEquiv_mk_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbSurfaceEquiv_mk_some_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {x : sctBox d n}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (hx : some x ∈ S) :
-- imply
  abbSurfaceEquiv hocc ⟨some x, hx⟩ = (⟨x, mem_abbPhysicalSurface_iff.mpr hx⟩ : abbPhysicalSurface d n S) := by
-- proof
  apply StatMech.Sharpness.abbSurfaceEquiv_mk_some hocc x hx

/--
[abbSurfaceEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbSurfaceEquiv_symm_apply_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {x : abbPhysicalSurface d n S}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty) :
-- imply
  (abbSurfaceEquiv hocc).symm x = (⟨some (x : sctBox d n), mem_abbPhysicalSurface_iff.mp x.property⟩ : S) := by
-- proof
  apply StatMech.Sharpness.abbSurfaceEquiv_symm_apply hocc x

/--
[abbSiteSurfaceEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbSiteSurfaceEquiv_apply_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {x : abbPhysicalSurface d n S} :
-- imply
  ((abbSiteSurfaceEquiv d n S x : abbSiteSurface d n S) : Site d) = ((x : sctBox d n) : Site d) := by
-- proof
  apply StatMech.Sharpness.abbSiteSurfaceEquiv_apply d n S x

/--
[abbSurfaceEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbSurfaceEquiv_adj_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {x y : S}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty) :
-- imply
  ((withGhost (sctBoxGraph d n)).induce (S : Set _)).Adj x y ↔ ((sctBoxGraph d n).induce (abbPhysicalSurface d n S : Set _)).Adj (abbSurfaceEquiv hocc x) (abbSurfaceEquiv hocc y) := by
-- proof
  apply StatMech.Sharpness.abbSurfaceEquiv_adj hocc x y

/--
[abbSiteSurfaceEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbSiteSurfaceEquiv_adj_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {x y : abbPhysicalSurface d n S} :
-- imply
  ((sctBoxGraph d n).induce (abbPhysicalSurface d n S : Set _)).Adj x y ↔ ((hypercubicLattice d).induce (abbSiteSurface d n S : Set _)).Adj (abbSiteSurfaceEquiv d n S x) (abbSiteSurfaceEquiv d n S y) := by
-- proof
  apply StatMech.Sharpness.abbSiteSurfaceEquiv_adj S x y

/--
[abbParams_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbParams_some_some_eq
  {d n : Nat}
  {x y : sctBox d n}
-- given
  (beta h : Real) :
-- imply
  abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h s(some x, some y) = if (sctBoxGraph d n).Adj x y then pBeta 1 beta else 0 := by
-- proof
  apply StatMech.Sharpness.abbParams_some_some d n beta h x y

/--
[abb_surface_conn_prob_eq_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_surface_conn_prob_eq_site_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {o x : S}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h) (connEvent (withGhost (sctBoxGraph d n)) (S : Set _) (o : Option (sctBox d n)) {(x : Option (sctBox d n))}) = probV (fun _ : Sym2 (abbSiteSurface d n S) ↦ pBeta 1 beta) (connEvent ((hypercubicLattice d).induce (abbSiteSurface d n S : Set _)) Set.univ (abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc o)) {abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc x)}) := by
-- proof
  apply StatMech.Sharpness.abb_surface_conn_prob_eq_site hocc o x beta h hbeta hh

/--
[abb_connWithinProb_eq_probV_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_connWithinProb_eq_probV_induce_eq
  {d : Nat}
  {p : NNReal}
  {T : Finset (Site d)}
  {x : Site d}
-- given
  (hp : p ≤ 1)
  (ho : origin d ∈ T)
  (hx : x ∈ T) :
-- imply
  connWithinProb d p hp T x = probV (fun _ : Sym2 T ↦ (p : Real)) (connEvent ((hypercubicLattice d).induce (T : Set _)) Set.univ (⟨origin d, ho⟩ : T) {(⟨x, hx⟩ : T)}) := by
-- proof
  apply StatMech.Sharpness.abb_connWithinProb_eq_probV_induce p hp T x ho hx

/--
[abb_bondParam_coe_eq_pBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_bondParam_coe_eq_pBeta_eq
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (bondParam beta : Real) = pBeta 1 beta := by
-- proof
  apply StatMech.Sharpness.abb_bondParam_coe_eq_pBeta beta hbeta

/--
[abb_surface_conn_prob_eq_connWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_surface_conn_prob_eq_connWithin_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {x : sctBox d n}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (ho : some (sctBoxOrigin d n) ∈ S)
  (hx : some x ∈ S)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h) (connEvent (withGhost (sctBoxGraph d n)) (S : Set _) (some (sctBoxOrigin d n)) {some x}) = connWithinProb d (bondParam beta) (bondParam_le_one beta) (abbSiteSurface d n S) (x : Site d) := by
-- proof
  apply StatMech.Sharpness.abb_surface_conn_prob_eq_connWithin hocc ho x hx beta h hbeta hh

/--
[abb_surface_avoids_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_surface_avoids_boundary_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {x : sctBox d n}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (hx : some x ∈ S) :
-- imply
  (x : Site d) ∉ vertexBoundary d n := by
-- proof
  apply StatMech.Sharpness.abb_surface_avoids_boundary hocc hx

/--
[abbSiteSurface_subset_innerBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbSiteSurface_subset_innerBox_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty) :
-- imply
  (abbSiteSurface d n S : Set (Site d)) ⊆ box d (n - 1) := by
-- proof
  apply StatMech.Sharpness.abbSiteSurface_subset_innerBox hocc

/--
[origin_mem_abbSiteSurface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma origin_mem_abbSiteSurface_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
-- given
  (ho : some (sctBoxOrigin d n) ∈ S) :
-- imply
  origin d ∈ abbSiteSurface d n S := by
-- proof
  apply StatMech.Sharpness.origin_mem_abbSiteSurface ho

/--
[abb_phi_ge_one_projected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_phi_ge_one_projected_eq
  {d n : Nat}
  {p : NNReal}
  {S : Finset (Option (sctBox d n))}
-- given
  (hp : p ≤ 1)
  (hgt : tildePc d < p)
  (ho : some (sctBoxOrigin d n) ∈ S) :
-- imply
  1 ≤ phi d p hp (abbSiteSurface d n S) := by
-- proof
  apply StatMech.Sharpness.abb_phi_ge_one_projected hp hgt ho

/--
[abbPairToSite_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbPairToSite_some_some_eq
  {d n : Nat}
  {x y : sctBox d n} :
-- imply
  abbPairToSite d n (some x, some y) = ((x : Site d), (y : Site d)) := by
-- proof
  apply StatMech.Sharpness.abbPairToSite_some_some d n x y

/--
[mem_abbPhysicalBoundaryPairs_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma mem_abbPhysicalBoundaryPairs_iff_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {q : Option (sctBox d n) × Option (sctBox d n)} :
-- imply
  q ∈ abbPhysicalBoundaryPairs d n S ↔ q ∈ shk_boundaryPairs (withGhost (sctBoxGraph d n)) S ∧ s(q.1, q.2) ∈ FieldGhostDict.origEdges (sctBoxGraph d n) := by
-- proof
  apply StatMech.Sharpness.mem_abbPhysicalBoundaryPairs_iff

/--
[abb_origEdge_endpoints_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abb_origEdge_endpoints_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : Option V}
-- given
  (h : s(a, b) ∈ FieldGhostDict.origEdges G) :
-- imply
  ∃ x y : V, a = some x ∧ b = some y := by
-- proof
  apply StatMech.Sharpness.abb_origEdge_endpoints_some G h

/--
[abbPairToSite_mem_boundaryEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbPairToSite_mem_boundaryEdges_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {q : Option (sctBox d n) × Option (sctBox d n)}
-- given
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (hq : q ∈ abbPhysicalBoundaryPairs d n S) :
-- imply
  abbPairToSite d n q ∈ boundaryEdges d (abbSiteSurface d n S) := by
-- proof
  apply StatMech.Sharpness.abbPairToSite_mem_boundaryEdges hocc hq

/--
[abbPairToSite_injectiveOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbPairToSite_injectiveOn_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))} :
-- imply
  Set.InjOn (abbPairToSite d n) (abbPhysicalBoundaryPairs d n S : Set _) := by
-- proof
  apply StatMech.Sharpness.abbPairToSite_injectiveOn

/--
[exists_abbPhysicalBoundaryPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma exists_abbPhysicalBoundaryPair_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
  {e : Site d × Site d}
-- given
  (hn : 0 < n)
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (he : e ∈ boundaryEdges d (abbSiteSurface d n S)) :
-- imply
  ∃ q ∈ abbPhysicalBoundaryPairs d n S, abbPairToSite d n q = e := by
-- proof
  apply StatMech.Sharpness.exists_abbPhysicalBoundaryPair hn hocc he

/--
[image_abbPhysicalBoundaryPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma image_abbPhysicalBoundaryPairs_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
-- given
  (hn : 0 < n)
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty) :
-- imply
  (abbPhysicalBoundaryPairs d n S).image (abbPairToSite d n) = boundaryEdges d (abbSiteSurface d n S) := by
-- proof
  apply StatMech.Sharpness.image_abbPhysicalBoundaryPairs hn hocc

/--
[abbPhi_eq_phi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbPhi_eq_phi_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
-- given
  (hn : 0 < n)
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (ho : some (sctBoxOrigin d n) ∈ S)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  abbPhi d n beta h S = phi d (bondParam beta) (bondParam_le_one beta) (abbSiteSurface d n S) := by
-- proof
  apply StatMech.Sharpness.abbPhi_eq_phi hn hocc ho beta h hbeta hh

/--
[abbPhi_ge_one_of_gt_tildePc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbPhi_ge_one_of_gt_tildePc_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
-- given
  (hn : 0 < n)
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (ho : some (sctBoxOrigin d n) ∈ S)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hgt : tildePc d < bondParam beta) :
-- imply
  1 ≤ abbPhi d n beta h S := by
-- proof
  apply StatMech.Sharpness.abbPhi_ge_one_of_gt_tildePc hn hocc ho beta h hbeta hh hgt

/--
[abbPhi_differentiableAt_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbPhi_differentiableAt_beta_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
-- given
  (beta h : Real) :
-- imply
  DifferentiableAt Real (fun b ↦ abbPhi d n b h S) beta := by
-- proof
  apply StatMech.Sharpness.abbPhi_differentiableAt_beta d n S beta h

/--
[abbPhi_ge_one_of_tildePc_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbPhi_ge_one_of_tildePc_le_eq
  {d n : Nat}
  {S : Finset (Option (sctBox d n))}
-- given
  (hn : 0 < n)
  (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty)
  (ho : some (sctBoxOrigin d n) ∈ S)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hge : tildePc d ≤ bondParam beta) :
-- imply
  1 ≤ abbPhi d n beta h S := by
-- proof
  apply StatMech.Sharpness.abbPhi_ge_one_of_tildePc_le hn hocc ho beta h hbeta hh hge

/--
[abbMag_meanfield_of_gt_tildePc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbMag_meanfield_of_gt_tildePc_eq
  {d n : Nat}
-- given
  (hn : 0 < n)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hgt : tildePc d < bondParam beta) :
-- imply
  1 - abbMag d n beta h ≤ beta * deriv (fun b ↦ abbMag d n b h) beta := by
-- proof
  apply StatMech.Sharpness.abbMag_meanfield_of_gt_tildePc hn beta h hbeta hh hgt

/--
[abbMag_meanfield_of_tildePc_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean)
-/
@[path]
private lemma abbMag_meanfield_of_tildePc_le_eq
  {d n : Nat}
-- given
  (hn : 0 < n)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hge : tildePc d ≤ bondParam beta) :
-- imply
  1 - abbMag d n beta h ≤ beta * deriv (fun b ↦ abbMag d n b h) beta := by
-- proof
  apply StatMech.Sharpness.abbMag_meanfield_of_tildePc_le hn beta h hbeta hh hge


-- created on 2026-10-23
