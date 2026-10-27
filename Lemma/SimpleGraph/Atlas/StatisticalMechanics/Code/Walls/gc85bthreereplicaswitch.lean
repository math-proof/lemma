import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc85b_mem_pcount_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_mem_pcount_filter_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W}
  {K₁ K₂ : Finset ι} :
-- imply
  (K₁, K₂) ∈ (m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B) ↔ (K₁ ⊆ m ∧ K₂ ⊆ m ∧ Disjoint K₁ K₂ ∧ sources ends K₁ = A ∧ sources ends K₂ = B) := by
-- proof
  apply StatMech.Walls.gc85b_mem_pcount_filter ends m A B K₁ K₂

/--
[gc85b_pcount_reroute_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_pcount_reroute_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W}
  {u v : W}
  {P : Finset ι}
-- given
  (huv : u ≠ v)
  (hPm : P ⊆ m)
  (hPsrc : sources ends P = {u, v}) :
-- imply
  #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B ∆ {u, v})) = #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B)) := by
-- proof
  apply StatMech.Walls.gc85b_pcount_reroute_eq ends m A B huv P hPm hPsrc

/--
[gc85b_pcount_univ_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_pcount_univ_mem_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {A B : Finset V}
  {S₁ S₂ : Finset (Copy G m)} :
-- imply
  (S₁, S₂) ∈ ((univ : Finset (Copy G m)).powerset ×ˢ (univ : Finset (Copy G m)).powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ RandomCurrent.sources (endsM G m) KK.1 = A ∧ RandomCurrent.sources (endsM G m) KK.2 = B) ↔ (Disjoint S₁ S₂ ∧ RandomCurrent.sources (endsM G m) S₁ = A ∧ RandomCurrent.sources (endsM G m) S₂ = B) := by
-- proof
  apply StatMech.Walls.gc85b_pcount_univ_mem G m A B S₁ S₂

/--
[gc85b_profile_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_profile_add_le_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {S₁ S₂ : Finset (Copy G m)}
  {e : ↥G.edgeFinset}
-- given
  (hdis : Disjoint S₁ S₂) :
-- imply
  profileFlux G m S₁ e + profileFlux G m S₂ e ≤ m e := by
-- proof
  apply StatMech.Walls.gc85b_profile_add_le G m hdis e

/--
[gc85b_fiber_pair_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_fiber_pair_count_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {e : ↥G.edgeFinset}
  {a b : ℕ}
-- given
  (hab : a + b ≤ m e) :
-- imply
  #((univ : Finset (Finset (Fin (m e)) × Finset (Fin (m e)))).filter (fun st => Disjoint st.1 st.2 ∧ #st.1 = a ∧ #st.2 = b)) = (m e).choose a * (m e - a).choose b := by
-- proof
  apply StatMech.Walls.gc85b_fiber_pair_count G m e a b hab

/--
[gc85b_pair_preimage_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_pair_preimage_count_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K₁ K₂ : ↥G.edgeFinset → ℕ}
-- given
  (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
-- imply
  #((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter (fun SS => Disjoint SS.1 SS.2 ∧ profileFlux G m SS.1 = K₁ ∧ profileFlux G m SS.2 = K₂)) = ∏ e : ↥G.edgeFinset, (m e).choose (K₁ e) * (m e - K₁ e).choose (K₂ e) := by
-- proof
  apply StatMech.Walls.gc85b_pair_preimage_count G m K₁ K₂ hK

/--
[gc85b_triple_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_triple_bridge_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {Θ : (↥G.edgeFinset → ℕ) → (↥G.edgeFinset → ℕ) → ℝ} :
-- imply
  (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}, (∏ e : ↥G.edgeFinset, (m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e)) • Θ K.1.1 K.1.2) = ∑ SS ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter (fun SS => Disjoint SS.1 SS.2), Θ (profileFlux G m SS.1) (profileFlux G m SS.2) := by
-- proof
  apply StatMech.Walls.gc85b_triple_bridge G m Θ

/--
[gc85b_tpsum_eq_pcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_tpsum_eq_pcount_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {A B : Finset V} :
-- imply
  gc15_tpsum G β J m A B = (gc85b_pcount (endsM G m) univ A B : ℝ) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Walls.gc85b_tpsum_eq_pcount G β J m A B

/--
[gc85b_threeGapCount_nonpos_of_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_threeGapCount_nonpos_of_bijection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hbij : gc85b_ThreeCurrentBijection ends m o x y g) :
-- imply
  gc85b_threeGapCount ends m o x y g ≤ 0 := by
-- proof
  apply StatMech.Walls.gc85b_threeGapCount_nonpos_of_bijection ends m o x y g hbij

/--
[gc85b_threeGapCount_nonpos_iff_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_threeGapCount_nonpos_iff_bijection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc85b_threeGapCount ends m o x y g ≤ 0 ↔ gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc85b_threeGapCount_nonpos_iff_bijection ends m o x y g

/--
[gc85b_pairwise_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_pairwise_insufficient_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  ∃ c00 c0og c0ox c0oy cogxg : ℤ, 0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00 ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy) := by
-- proof
  apply StatMech.Walls.gc85b_pairwise_insufficient

/--
[gc85b_gc15_threeGap_eq_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_gc15_threeGap_eq_count_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  gc15_threeGap G β h o x y m = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
-- proof
  apply StatMech.Walls.gc85b_gc15_threeGap_eq_count G β h o x y hox hoy hxy m hm

/--
[gc85b_gc15_threeGap_nonpos_of_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_gc15_threeGap_nonpos_of_bijection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbij : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none) :
-- imply
  gc15_threeGap G β h o x y m ≤ 0 := by
-- proof
  apply StatMech.Walls.gc85b_gc15_threeGap_nonpos_of_bijection G β h hβ hh o x y hox hoy hxy m hbij

/--
[gc85b_ursell_nonpos_of_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_ursell_nonpos_of_bijection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbij : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc85b_ursell_nonpos_of_bijection G β h hβ hh o x y hox hoy hxy hbij hsupp

/--
[gc85b_three_replica_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean)
-/
@[path]
private lemma gc85b_three_replica_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc15_threeGap G β h o x y m = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m)) ∧ (∃ c00 c0og c0ox c0oy cogxg : ℤ, 0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00 ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy)) ∧ ((∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none) → gc82_ThreeGapAllConnSupported G β h o x y → eg_ursell3 G β h o x y ≤ 0) := by
-- proof
  apply StatMech.Walls.gc85b_three_replica_status G β h hβ hh o x y hox hoy hxy


-- created on 2026-10-23
