import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldPercoInhom.Part5
open Finset SimpleGraph Set StatMech StatMech.Sharpness


/--
[mpi_mem_blockedSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_mem_blockedSet_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {omega : ConfigSpace (Sym2 V)}
  {x : V} :
-- imply
  x ∈ mpiBlockedSet G B omega ↔ ¬ ConnToSet G omega Set.univ x B := by
-- proof
  apply StatMech.Sharpness.mpi_mem_blockedSet_iff G B omega x

/--
[mpi_not_mem_blockedSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_not_mem_blockedSet_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {omega : ConfigSpace (Sym2 V)}
  {x : V} :
-- imply
  x ∉ mpiBlockedSet G B omega ↔ ConnToSet G omega Set.univ x B := by
-- proof
  apply StatMech.Sharpness.mpi_not_mem_blockedSet_iff G B omega x

/--
[mpi_not_crossing_iff_mem_blockedSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_not_crossing_iff_mem_blockedSet_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {B : Set V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  omega ∉ mpiCrossingEvent G o B ↔ o ∈ mpiBlockedSet G B omega := by
-- proof
  apply StatMech.Sharpness.mpi_not_crossing_iff_mem_blockedSet G o B omega

/--
[mpi_connToSet_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_connToSet_of_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (hxy : G.Adj x y)
  (hopen : omega s(x, y) = true)
  (hy : ConnToSet G omega Set.univ y B) :
-- imply
  ConnToSet G omega Set.univ x B := by
-- proof
  apply StatMech.Sharpness.mpi_connToSet_of_adj G B omega hxy hopen hy

/--
[mpi_boundary_edge_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_boundary_edge_closed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {omega : ConfigSpace (Sym2 V)}
  {S : Finset V}
  {x y : V}
-- given
  (hS : mpiBlockedSet G B omega = S)
  (hx : x ∈ S)
  (hy : y ∉ S)
  (hxy : G.Adj x y) :
-- imply
  omega s(x, y) = false := by
-- proof
  apply StatMech.Sharpness.mpi_boundary_edge_closed G B omega hS hx hy hxy

/--
[mpi_le_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_le_setOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  omega ≤ setOpen e omega := by
-- proof
  apply StatMech.Sharpness.mpi_le_setOpen G e omega

/--
[mpi_boundary_edge_isPivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_boundary_edge_isPivotal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {B : Set V}
  {omega : ConfigSpace (Sym2 V)}
  {S : Finset V}
  {x y : V}
-- given
  (hS : mpiBlockedSet G B omega = S)
  (ho : o ∈ S)
  (hx : x ∈ S)
  (hy : y ∉ S)
  (hxy : G.Adj x y)
  (hox : ConnToSet G omega (S : Set V) o {x}) :
-- imply
  IsPivotal s(x, y) (mpiCrossingEvent G o B) omega := by
-- proof
  apply StatMech.Sharpness.mpi_boundary_edge_isPivotal G o B omega hS ho hx hy hxy hox

/--
[mpi_internalEdge_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_internalEdge_mk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Set V}
  {x y : V}
-- given
  (hx : x ∈ S)
  (hy : y ∈ S) :
-- imply
  s(x, y) ∈ mpiInternalEdges S := by
-- proof
  apply StatMech.Sharpness.mpi_internalEdge_mk G hx hy

/--
[mpi_not_internalEdge_mk_of_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_not_internalEdge_mk_of_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Set V}
  {x y : V}
-- given
  (hy : y ∉ S) :
-- imply
  s(x, y) ∉ mpiInternalEdges S := by
-- proof
  apply StatMech.Sharpness.mpi_not_internalEdge_mk_of_right G hy

/--
[mpi_connWithin_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_connWithin_transfer_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega omega' : ConfigSpace (Sym2 V)}
  {S : Set V}
  {a b : S}
-- given
  (hagree : ∀ e ∈ mpiInternalEdges S, omega e = omega' e)
  (h : ConnWithin G omega S a b) :
-- imply
  ConnWithin G omega' S a b := by
-- proof
  apply StatMech.Sharpness.mpi_connWithin_transfer G hagree h

/--
[mpi_connEvent_determined_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_connEvent_determined_internal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o x : V} :
-- imply
  DeterminedBy (connEvent G (S : Set V) o {x}) (mpiInternalEdges (S : Set V)) := by
-- proof
  apply StatMech.Sharpness.mpi_connEvent_determined_internal G S o x

/--
[mpi_connEventSet_determined_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_connEventSet_determined_internal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o : V}
  {B : Set V} :
-- imply
  DeterminedBy (connEvent G (S : Set V) o B) (mpiInternalEdges (S : Set V)) := by
-- proof
  apply StatMech.Sharpness.mpi_connEventSet_determined_internal G S o B

/--
[mpi_target_not_mem_blockedSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_target_not_mem_blockedSet_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {omega : ConfigSpace (Sym2 V)}
  {b : V}
-- given
  (hb : b ∈ B) :
-- imply
  b ∉ mpiBlockedSet G B omega := by
-- proof
  apply StatMech.Sharpness.mpi_target_not_mem_blockedSet G B omega hb

/--
[mpi_surfaceEvent_nonempty_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_surfaceEvent_nonempty_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {S : Finset V}
-- given
  (hocc : (mpiSurfaceEvent G B S).Nonempty) :
-- imply
  Disjoint (S : Set V) B := by
-- proof
  apply StatMech.Sharpness.mpi_surfaceEvent_nonempty_disjoint G B S hocc

/--
[mpi_outside_connection_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_outside_connection_walk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {omega : ConfigSpace (Sym2 V)}
  {S : Finset V}
  {y : V}
-- given
  (hS : mpiBlockedSet G B omega = S)
  (hy : y ∉ S) :
-- imply
  ∃ b ∈ B, ∃ p : (openSub G omega).Walk y b, ∀ z ∈ p.support, z ∉ S := by
-- proof
  apply StatMech.Sharpness.mpi_outside_connection_walk G B omega hS hy

/--
[mpi_outside_conn_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_outside_conn_transfer_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {S : Finset V}
  {omega omega' : ConfigSpace (Sym2 V)}
  {y : V}
-- given
  (hS : mpiBlockedSet G B omega = S)
  (hagree : agreeOn (mpiInternalEdges (S : Set V))ᶜ omega omega')
  (hy : y ∉ S) :
-- imply
  ConnToSet G omega' Set.univ y B := by
-- proof
  apply StatMech.Sharpness.mpi_outside_conn_transfer G hS hagree hy

/--
[mpi_inside_not_conn_of_exterior_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_inside_not_conn_of_exterior_agree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {S : Finset V}
  {omega omega' : ConfigSpace (Sym2 V)}
  {x : V}
-- given
  (hS : mpiBlockedSet G B omega = S)
  (hagree : agreeOn (mpiInternalEdges (S : Set V))ᶜ omega omega')
  (hx : x ∈ S) :
-- imply
  ¬ ConnToSet G omega' Set.univ x B := by
-- proof
  apply StatMech.Sharpness.mpi_inside_not_conn_of_exterior_agree G hS hagree hx

/--
[mpi_surfaceEvent_determined_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_surfaceEvent_determined_exterior_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Set V}
  {S : Finset V} :
-- imply
  DeterminedBy (mpiSurfaceEvent G B S) (mpiInternalEdges (S : Set V))ᶜ := by
-- proof
  apply StatMech.Sharpness.mpi_surfaceEvent_determined_exterior G B S

/--
[mpi_conn_surface_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_conn_surface_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {B : Set V}
  {S : Finset V}
  {o x : V} :
-- imply
  wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) o {x} ∩ mpiSurfaceEvent G B S) = wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) o {x}) * wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
-- proof
  apply StatMech.Sharpness.mpi_conn_surface_factor G beta J B S o x

/--
[mpi_wprob_crossing_compl_eq_sum_surfaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_wprob_crossing_compl_eq_sum_surfaces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phi : Sym2 V → Bool → ℝ}
  {o : V}
  {B : Set V}
-- given
  (hphi : ∀ e, phi e false + phi e true = 1) :
-- imply
  wprob phi (mpiCrossingEvent G o B)ᶜ = ∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S), wprob phi (mpiSurfaceEvent G B S) := by
-- proof
  apply StatMech.Sharpness.mpi_wprob_crossing_compl_eq_sum_surfaces G phi hphi o B

/--
[mpi_wprob_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_wprob_compl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phi : Sym2 V → Bool → ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hphi : ∀ e, phi e false + phi e true = 1) :
-- imply
  wprob phi Aᶜ = 1 - wprob phi A := by
-- proof
  apply StatMech.Sharpness.mpi_wprob_compl G phi hphi A

/--
[mpi_perSurface_eq_phi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_perSurface_eq_phi_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set V}
  {S : Finset V} :
-- imply
  (∑ q ∈ shk_boundaryPairs G S, (1 - Real.exp (-beta * J s(q.1, q.2))) * wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) = mpiPhi G beta J o S * wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
-- proof
  apply StatMech.Sharpness.mpi_perSurface_eq_phi G beta J o B S

/--
[mpi_openWeight_div_beta_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_openWeight_div_beta_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta Je : ℝ}
-- given
  (hbeta : 0 < beta)
  (hJe : 0 ≤ Je) :
-- imply
  (1 / beta) * (1 - Real.exp (-beta * Je)) ≤ Je := by
-- proof
  apply StatMech.Sharpness.mpi_openWeight_div_beta_le G beta Je hbeta hJe

/--
[mpi_phi_surface_le_boundaryJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_phi_surface_le_boundaryJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set V}
  {S : Finset V}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (1 / beta) * mpiPhi G beta J o S * wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) ≤ ∑ q ∈ shk_boundaryPairs G S, J s(q.1, q.2) * wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) := by
-- proof
  apply StatMech.Sharpness.mpi_phi_surface_le_boundaryJ G beta J hbeta hJ o B S

/--
[mpi_setClosed_eq_of_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_setClosed_eq_of_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (he : omega e = false) :
-- imply
  setClosed e omega = omega := by
-- proof
  apply StatMech.Sharpness.mpi_setClosed_eq_of_false G he

/--
[mpi_pivotalClosed_subset_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_pivotalClosed_subset_compl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hA : IsIncreasing A) :
-- imply
  mpiPivotalClosed e A ⊆ Aᶜ := by
-- proof
  apply StatMech.Sharpness.mpi_pivotalClosed_subset_compl G hA

/--
[mpi_conn_surface_subset_pivotalClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_conn_surface_subset_pivotalClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {B : Set V}
  {S : Finset V}
  {q : V × V}
-- given
  (ho : o ∈ S)
  (hq : q ∈ shk_boundaryPairs G S) :
-- imply
  connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S ⊆ mpiPivotalClosed s(q.1, q.2) (mpiCrossingEvent G o B) := by
-- proof
  apply StatMech.Sharpness.mpi_conn_surface_subset_pivotalClosed G o B S ho hq

/--
[mpi_wprob_eq_sum_inter_surfaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_wprob_eq_sum_inter_surfaces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phi : Sym2 V → Bool → ℝ}
  {o : V}
  {B : Set V}
  {C : Set (ConfigSpace (Sym2 V))}
-- given
  (hC : C ⊆ (mpiCrossingEvent G o B)ᶜ) :
-- imply
  wprob phi C = ∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S), wprob phi (C ∩ mpiSurfaceEvent G B S) := by
-- proof
  apply StatMech.Sharpness.mpi_wprob_eq_sum_inter_surfaces G phi o B C hC

/--
[mpi_boundaryJ_le_edgePivotal_surface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_boundaryJ_le_edgePivotal_surface_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set V}
  {S : Finset V}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e)
  (ho : o ∈ S) :
-- imply
  (∑ q ∈ shk_boundaryPairs G S, J s(q.1, q.2) * wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) ≤ ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S) := by
-- proof
  apply StatMech.Sharpness.mpi_boundaryJ_le_edgePivotal_surface G beta J hbeta hJ o B S ho

/--
[mpi_surface_reassembly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_surface_reassembly_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set V}
  {m : ℝ}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hm : ∀ S : Finset V, o ∈ S → m ≤ mpiPhi G beta J o S) :
-- imply
  (1 / beta) * m * (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤ ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
-- proof
  apply StatMech.Sharpness.mpi_surface_reassembly G beta J hbeta hJ o B m hm

/--
[mpi_surface_reassembly_of_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_surface_reassembly_of_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set V}
  {m : ℝ}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hm : ∀ S : Finset V, o ∈ S → (mpiSurfaceEvent G B S).Nonempty → m ≤ mpiPhi G beta J o S) :
-- imply
  (1 / beta) * m * (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤ ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
-- proof
  apply StatMech.Sharpness.mpi_surface_reassembly_of_nonempty G beta J hbeta hJ o B m hm

/--
[mpi_pweight_eq_edge_mul_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_pweight_eq_edge_mul_off_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  pweight (shk_edgeLaw beta J) omega = shk_edgeLaw beta J e (omega e) * mpiWeightOff beta J e omega := by
-- proof
  apply StatMech.Sharpness.mpi_pweight_eq_edge_mul_off G beta J e omega

/--
[mpi_weightOff_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_weightOff_congr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {e : Sym2 V}
  {omega omega' : ConfigSpace (Sym2 V)}
-- given
  (h : ∀ j, j ≠ e → omega j = omega' j) :
-- imply
  mpiWeightOff beta J e omega = mpiWeightOff beta J e omega' := by
-- proof
  apply StatMech.Sharpness.mpi_weightOff_congr G beta J e h

/--
[mpi_hasDerivAt_pweight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_hasDerivAt_pweight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {beta : ℝ}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  HasDerivAt (fun b => pweight (shk_edgeLaw b J) omega) (∑ e, mpiWeightOff beta J e omega * (if omega e then J e * Real.exp (-(beta * J e)) else -(J e * Real.exp (-(beta * J e))))) beta := by
-- proof
  apply StatMech.Sharpness.mpi_hasDerivAt_pweight G J beta omega

/--
[mpi_perEdge_beta_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_perEdge_beta_pivotal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
  {e : Sym2 V}
-- given
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * (mpiWeightOff beta J e omega * (if omega e then J e * Real.exp (-(beta * J e)) else -(J e * Real.exp (-(beta * J e)))))) = J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e A) := by
-- proof
  apply StatMech.Sharpness.mpi_perEdge_beta_pivotal G beta J A hA e

/--
[mpi_hasDerivAt_wprob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_hasDerivAt_wprob_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hA : IsIncreasing A) :
-- imply
  HasDerivAt (fun b => wprob (shk_edgeLaw b J) A) (∑ e, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e A)) beta := by
-- proof
  apply StatMech.Sharpness.mpi_hasDerivAt_wprob G beta J A hA

/--
[mpi_meanfield_perco](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_meanfield_perco_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set V}
  {m : ℝ}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hm : ∀ S : Finset V, o ∈ S → m ≤ mpiPhi G beta J o S) :
-- imply
  HasDerivAt (fun b => wprob (shk_edgeLaw b J) (mpiCrossingEvent G o B)) (∑ e, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e (mpiCrossingEvent G o B))) beta ∧ (1 / beta) * m * (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤ ∑ e, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
-- proof
  apply StatMech.Sharpness.mpi_meanfield_perco G beta J hbeta hJ o B m hm

/--
[mpi_meanfield_perco_of_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_meanfield_perco_of_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set V}
  {m : ℝ}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hm : ∀ S : Finset V, o ∈ S → (mpiSurfaceEvent G B S).Nonempty → m ≤ mpiPhi G beta J o S) :
-- imply
  HasDerivAt (fun b => wprob (shk_edgeLaw b J) (mpiCrossingEvent G o B)) (∑ e, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e (mpiCrossingEvent G o B))) beta ∧ (1 / beta) * m * (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤ ∑ e, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
-- proof
  apply StatMech.Sharpness.mpi_meanfield_perco_of_nonempty G beta J hbeta hJ o B m hm

/--
[mpi_meanfield_perco_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean)
-/
@[path]
private lemma mpi_meanfield_perco_of_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {o : V}
  {B : Set V}
  {m : ℝ}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hm : ∀ S : Finset V, o ∈ S → Disjoint (S : Set V) B → m ≤ mpiPhi G beta J o S) :
-- imply
  HasDerivAt (fun b => wprob (shk_edgeLaw b J) (mpiCrossingEvent G o B)) (∑ e, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e (mpiCrossingEvent G o B))) beta ∧ (1 / beta) * m * (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤ ∑ e, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
-- proof
  apply StatMech.Sharpness.mpi_meanfield_perco_of_disjoint G beta J hbeta hJ o B m hm


-- created on 2026-10-23
