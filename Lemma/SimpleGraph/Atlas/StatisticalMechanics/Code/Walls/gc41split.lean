import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc41split.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc41_mem_sigmaFinsetEquivPi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_mem_sigmaFinsetEquivPi_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {γ : E → Type*}
  {S : Finset (Σ e : E, γ e)}
  {e : E}
  {b : γ e} :
-- imply
  b ∈ sigmaFinsetEquivPi S e ↔ (⟨e, b⟩ : Σ e, γ e) ∈ S := by
-- proof
  apply StatMech.Walls.gc41_mem_sigmaFinsetEquivPi G S e b

/--
[gc41_disj_fiberwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_disj_fiberwise_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {γ : E → Type*}
  {S₁ S₂ : Finset (Σ e : E, γ e)} :
-- imply
  S₂ ⊆ univ \ S₁ ↔ ∀ e, sigmaFinsetEquivPi S₂ e ⊆ univ \ sigmaFinsetEquivPi S₁ e := by
-- proof
  apply StatMech.Walls.gc41_disj_fiberwise G S₁ S₂

/--
[gc41_perFiber_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_perFiber_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {γ : E → Type*}
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  {n k1 k2 : ℕ}
-- given
  (h : Fintype.card α = n) :
-- imply
  #((univ : Finset (Finset α × Finset α)).filter (fun p => p.2 ⊆ univ \ p.1 ∧ #p.1 = k1 ∧ #p.2 = k2)) = n.choose k1 * (n - k1).choose k2 := by
-- proof
  apply StatMech.Walls.gc41_perFiber_count G α n k1 k2 h

/--
[gc41_pi_pair_profile_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_pi_pair_profile_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {γ : E → Type*}
  {K₁ K₂ : E → ℕ} :
-- imply
  #((univ : Finset (Finset (Σ e : E, γ e) × Finset (Σ e : E, γ e))).filter (fun p => p.2 ⊆ univ \ p.1 ∧ (fun e => #(sigmaFinsetEquivPi p.1 e)) = K₁ ∧ (fun e => #(sigmaFinsetEquivPi p.2 e)) = K₂)) = ∏ e : E, ((Fintype.card (γ e)).choose (K₁ e) * (Fintype.card (γ e) - K₁ e).choose (K₂ e)) := by
-- proof
  apply StatMech.Walls.gc41_pi_pair_profile_count G K₁ K₂

/--
[gc41_pair_profile_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_pair_profile_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K₁ K₂ : ↥G.edgeFinset → ℕ} :
-- imply
  #((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter (fun p => p.2 ⊆ univ \ p.1 ∧ profileFlux G m p.1 = K₁ ∧ profileFlux G m p.2 = K₂)) = ∏ e : ↥G.edgeFinset, ((m e).choose (K₁ e) * (m e - K₁ e).choose (K₂ e)) := by
-- proof
  apply StatMech.Walls.gc41_pair_profile_count G m K₁ K₂

/--
[gc41_pairProfile_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_pairProfile_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {S₁ S₂ : Finset (Copy G m)}
-- given
  (hdisj : S₂ ⊆ univ \ S₁) :
-- imply
  ∀ e, profileFlux G m S₁ e + profileFlux G m S₂ e ≤ m e := by
-- proof
  apply StatMech.Walls.gc41_pairProfile_le G m S₁ S₂ hdisj

/--
[gc41_fin_filter_range_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_fin_filter_range_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n a b : ℕ}
-- given
  (h : a + b ≤ n) :
-- imply
  #((univ : Finset (Fin n)).filter (fun j => a ≤ j.val ∧ j.val < a + b)) = b := by
-- proof
  apply StatMech.Walls.gc41_fin_filter_range_card G n a b h

/--
[gc41_profile_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_profile_range_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K₁ K₂ : ↥G.edgeFinset → ℕ}
-- given
  (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
-- imply
  profileFlux G m (univ.filter (fun i : FluxEdgeCopy.Copy G m => K₁ i.1 ≤ i.2.val ∧ i.2.val < K₁ i.1 + K₂ i.1)) = K₂ := by
-- proof
  apply StatMech.Walls.gc41_profile_range G m K₁ K₂ hK

/--
[gc41_pair_edgecopy_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_pair_edgecopy_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [AddCommMonoid M]
  {m : ↥G.edgeFinset → ℕ}
  {Θ : (↥G.edgeFinset → ℕ) → (↥G.edgeFinset → ℕ) → M} :
-- imply
  (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}, (∏ e : ↥G.edgeFinset, ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e))) • Θ K.1.1 K.1.2) = ∑ p ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter (fun p => p.2 ⊆ univ \ p.1), Θ (profileFlux G m p.1) (profileFlux G m p.2) := by
-- proof
  apply StatMech.Walls.gc41_pair_edgecopy_bridge G m Θ

/--
[gc41_tpsum_eq_pairCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_tpsum_eq_pairCount_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {A B : Finset V} :
-- imply
  gc15_tpsum G β J m A B = (#((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter (fun p => p.2 ⊆ univ \ p.1 ∧ RandomCurrent.sources (endsM G m) p.1 = A ∧ RandomCurrent.sources (endsM G m) p.2 = B)) : ℝ) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Walls.gc41_tpsum_eq_pairCount G β J m A B

/--
[gc41_sd_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_sd_third_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq W]
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  ({o, x, y, g} : Finset W) ∆ {o, g} ∆ {x, g} = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc41_sd_third G o x y g hox hoy hog hxy hxg hyg

/--
[gc41_pairCount_eq_NR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_pairCount_eq_NR_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
-- imply
  #((univ : Finset (Finset ι × Finset ι)).filter (fun p => p.2 ⊆ univ \ p.1 ∧ sources ends p.1 = ({o, g} : Finset W) ∧ sources ends p.2 = ({x, g} : Finset W))) = gc40_NR ends o x y g := by
-- proof
  apply StatMech.Walls.gc41_pairCount_eq_NR G ends hox hoy hog hxy hxg hyg huniv

/--
[gc41_NR_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_NR_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) ≠ ({o, x, y, g} : Finset W)) :
-- imply
  gc40_NR ends o x y g = 0 := by
-- proof
  apply StatMech.Walls.gc41_NR_eq_zero G ends hox hoy hog hxy hxg hyg huniv

/--
[gc41_csTriple_eq_NRsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_csTriple_eq_NRsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc39_csTriple G β h o x y = ∑' m : ↥(withGhost G).edgeFinset → ℕ, (gc40_NR (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
-- proof
  apply StatMech.Walls.gc41_csTriple_eq_NRsum G β h o x y hox hoy hxy

/--
[gc41_allConnTripleSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_allConnTripleSum_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {o x y g : V} :
-- imply
  gc41_allConnTripleSum G β J A o x y g = gc38_sourcePairAllConnSum G β J A o x y g * currentSum G β J ∅ := by
-- proof
  apply StatMech.Walls.gc41_allConnTripleSum_eq G β J A o x y g

/--
[gc41_gatedTriple_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_gatedTriple_superposition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V}
  {Wg : (↥G.edgeFinset → ℕ) → ℝ}
-- given
  (hWb : ∀ p, |Wg p| ≤ 1) :
-- imply
  (∑' z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), ((if sources G (ofEdgeFun G z.1) = A then weight G β J (ofEdgeFun G z.1) else 0) * (if sources G (ofEdgeFun G z.2.1) = B then weight G β J (ofEdgeFun G z.2.1) else 0) * (if sources G (ofEdgeFun G z.2.2) = C then weight G β J (ofEdgeFun G z.2.2) else 0)) * Wg (fun e => z.1 e + z.2.1 e)) = ∑' m : ↥G.edgeFinset → ℕ, (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}, (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0) * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = C then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0) * Wg (fun e => K.1.1 e + K.1.2 e)) := by
-- proof
  apply StatMech.Walls.gc41_gatedTriple_superposition G β J A B C Wg hWb

/--
[gc41_profileFlux_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_profileFlux_union_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {S₁ S₂ : Finset (Copy G m)}
-- given
  (hd : S₂ ⊆ univ \ S₁) :
-- imply
  profileFlux G m (S₁ ∪ S₂) = fun e => profileFlux G m S₁ e + profileFlux G m S₂ e := by
-- proof
  apply StatMech.Walls.gc41_profileFlux_union G m S₁ S₂ hd

/--
[gc41_allConnSplit_eq_NL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_allConnSplit_eq_NL_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {o x y g : V} :
-- imply
  (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}, (if sources G (ofEdgeFun G K.1.1) = ({o, x, y, g} : Finset V) then weight G β J (ofEdgeFun G K.1.1) else 0) * (if sources G (ofEdgeFun G K.1.2) = (∅ : Finset V) then weight G β J (ofEdgeFun G K.1.2) else 0) * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = (∅ : Finset V) then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0) * (if CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o x ∧ CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o y ∧ CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o g then 1 else 0)) = (gc40_NL (endsM G m) o x y g : ℝ) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Walls.gc41_allConnSplit_eq_NL G β J m o x y g

/--
[gc41_Z0allConn_eq_NLsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_Z0allConn_eq_NLsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  gc15_Z0 G β h * gc39_allConnSum G β h o x y = ∑' m : ↥(withGhost G).edgeFinset → ℕ, (gc40_NL (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
-- proof
  apply StatMech.Walls.gc41_Z0allConn_eq_NLsum G β h o x y

/--
[gc41_NR_eq_tFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_NR_eq_tFiber_eq
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
  (hxy : x ≠ y) :
-- imply
  (gc40_NR (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) = gc15_tFiber (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, none}) ({some x, none}) ({some y, none}) m := by
-- proof
  apply StatMech.Walls.gc41_NR_eq_tFiber G β h o x y hox hoy hxy m

/--
[gc41_NL_le_pairCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_NL_le_pairCount_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  gc40_NL ends o x y g ≤ #((univ : Finset (Finset ι × Finset ι)).filter (fun p => p.2 ⊆ univ \ p.1 ∧ sources ends p.1 = ({o, x, y, g} : Finset W) ∧ sources ends p.2 = (∅ : Finset W))) := by
-- proof
  apply StatMech.Walls.gc41_NL_le_pairCount G ends o x y g

/--
[gc41_NL_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_NL_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (huniv : sources ends (univ : Finset ι) ≠ ({o, x, y, g} : Finset W)) :
-- imply
  gc40_NL ends o x y g = 0 := by
-- proof
  apply StatMech.Walls.gc41_NL_eq_zero G ends huniv

/--
[gc41_NLweight_le_tFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_NLweight_le_tFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  (gc40_NL (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) ≤ gc15_tFiber (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, none}) ∅ ∅ m := by
-- proof
  apply StatMech.Walls.gc41_NLweight_le_tFiber G β h hβ hh o x y m

/--
[gc41_NLweight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_NLweight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ (gc40_NL (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
-- proof
  apply StatMech.Walls.gc41_NLweight_nonneg G β h hβ hh o x y m

/--
[gc41_improvedBound_of_countIneq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean)
-/
@[path]
private lemma gc41_improvedBound_of_countIneq_eq
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
  (hcnt : ∀ m : ↥(withGhost G).edgeFinset → ℕ, gc39_ThreeColouringCountIneq (endsM (withGhost G) m) (some o) (some x) (some y) none) :
-- imply
  gc39_ThreeReplicaImprovedBound G β h o x y := by
-- proof
  apply StatMech.Walls.gc41_improvedBound_of_countIneq G β h hβ hh o x y hox hoy hxy hcnt


-- created on 2026-10-23
