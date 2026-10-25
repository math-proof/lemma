import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc19switching.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc19_eref_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_eref_le_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {p : ↥S.edgeFinset → ℕ}
  {P : Finset (Sym2 V)}
  {K : ↥S.edgeFinset → ℕ}
-- given
  (hK : ∀ e, K e ≤ p e) :
-- imply
  ∀ e, gc19_eref S p P K e ≤ p e := by
-- proof
  apply StatMech.Walls.gc19_eref_le S p P hK

/--
[gc19_eref_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_eref_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {p : ↥S.edgeFinset → ℕ}
  {P : Finset (Sym2 V)}
  {K : ↥S.edgeFinset → ℕ}
-- given
  (hK : ∀ e, K e ≤ p e) :
-- imply
  gc19_eref S p P (gc19_eref S p P K) = K := by
-- proof
  apply StatMech.Walls.gc19_eref_involutive S p P hK

/--
[gc19_ofEdgeFun_eref](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_ofEdgeFun_eref_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {p K : ↥S.edgeFinset → ℕ}
  {P : Finset (Sym2 V)} :
-- imply
  ofEdgeFun S (gc19_eref S p P K) = StatMech.Ising.reflect (ofEdgeFun S p) P (ofEdgeFun S K) := by
-- proof
  apply StatMech.Walls.gc19_ofEdgeFun_eref S p K P

/--
[gc19_ofEdgeFun_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_ofEdgeFun_sub_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {p K : ↥S.edgeFinset → ℕ} :
-- imply
  ofEdgeFun S (fun e => p e - K e) = (fun e => ofEdgeFun S p e - ofEdgeFun S K e) := by
-- proof
  apply StatMech.Walls.gc19_ofEdgeFun_sub S p K

/--
[gc19_ref2_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_ref2_weight_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {P : Finset (Sym2 V)}
-- given
  (K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}) :
-- imply
  weight S β J (ofEdgeFun S (gc19_eref S (fun e => m e - K.1.1 e) P K.1.2)) * weight S β J (ofEdgeFun S (fun e => m e - K.1.1 e - gc19_eref S (fun e => m e - K.1.1 e) P K.1.2 e)) = weight S β J (ofEdgeFun S K.1.2) * weight S β J (ofEdgeFun S (fun e => m e - K.1.1 e - K.1.2 e)) := by
-- proof
  apply StatMech.Walls.gc19_ref2_weight S β J m P K

/--
[gc19_ref2_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_ref2_sources_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {m : ↥S.edgeFinset → ℕ}
  {P : Finset (Sym2 V)}
-- given
  (K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e})
  (hPE : P ⊆ S.edgeFinset)
  (hPodd : ∀ e ∈ P, Odd ((ofEdgeFun S (fun e => m e - K.1.1 e)) e)) :
-- imply
  sources S (ofEdgeFun S (gc19_eref S (fun e => m e - K.1.1 e) P K.1.2)) = sources S (ofEdgeFun S K.1.2) ∆ srcP P := by
-- proof
  apply StatMech.Walls.gc19_ref2_sources S m P K hPE hPodd

/--
[gc19_tpsum_firstSlot_switch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_tpsum_firstSlot_switch_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {A B : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hconn : ∀ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₂.1) = B → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) u v) :
-- imply
  gc15_tpsum S β J m (A ∆ {u, v}) B = gc15_tpsum S β J m A B := by
-- proof
  apply StatMech.Walls.gc19_tpsum_firstSlot_switch S β J m A B huv hconn

/--
[gc19_tpsum_secondSlot_switch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_tpsum_secondSlot_switch_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {A B : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hconn : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₁.1) = A → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) u v) :
-- imply
  gc15_tpsum S β J m A (B ∆ {u, v}) = gc15_tpsum S β J m A B := by
-- proof
  apply StatMech.Walls.gc19_tpsum_secondSlot_switch S β J m A B huv hconn

/--
[gc19_tpsum_secondSlot_directSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_tpsum_secondSlot_directSwitch_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {A B : Finset V}
  {P : Finset (Sym2 V)}
-- given
  (hPE : P ⊆ S.edgeFinset)
  (hPodd : ∀ K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}, ∀ e ∈ P, Odd ((ofEdgeFun S (fun e => m e - K.1.1 e)) e)) :
-- imply
  gc15_tpsum S β J m A (B ∆ srcP P) = gc15_tpsum S β J m A B := by
-- proof
  apply StatMech.Walls.gc19_tpsum_secondSlot_directSwitch S β J m A B P hPE hPodd

/--
[gc19_tpsum_starPair_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_tpsum_starPair_collapse_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hconn : ∀ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₂.1) = ∅ → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) u v) :
-- imply
  gc15_tpsum S β J m ∅ {u, v} = gc15_tpsum S β J m ∅ ∅ := by
-- proof
  apply StatMech.Walls.gc19_tpsum_starPair_collapse S β J m huv hconn

/--
[gc19_tpsum_fifth_reduce_to_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_tpsum_fifth_reduce_to_base_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {o x g : V}
-- given
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (hcr1 : ∀ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₂.1) = {x, g} → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) o g)
  (hcr2 : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₁.1) = ∅ → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) x g) :
-- imply
  gc15_tpsum S β J m {o, g} {x, g} = gc15_tpsum S β J m ∅ ∅ := by
-- proof
  apply StatMech.Walls.gc19_tpsum_fifth_reduce_to_base S β J m hog hxg hcr1 hcr2

/--
[gc19_cert_zero_of_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_cert_zero_of_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {o x y g : V}
-- given
  (hog : o ≠ g)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxg : x ≠ g)
  (hOg : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₁.1) = ∅ → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) o g)
  (hOx : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₁.1) = ∅ → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) o x)
  (hOy : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₁.1) = ∅ → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) o y)
  (hcr1 : ∀ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₂.1) = {x, g} → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) o g)
  (hcr2 : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources S (ofEdgeFun S K₁.1) = ∅ → connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) x g) :
-- imply
  gc15_tpsum S β J m ∅ ∅ - gc15_tpsum S β J m ∅ {o, g} - gc15_tpsum S β J m ∅ {o, x} - gc15_tpsum S β J m ∅ {o, y} + 2 * gc15_tpsum S β J m {o, g} {x, g} = 0 := by
-- proof
  apply StatMech.Walls.gc19_cert_zero_of_allConn S β J m hog hox hoy hxg hOg hOx hOy hcr1 hcr2

/--
[gc19_conn_of_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_conn_of_sourcePair_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {m : ↥S.edgeFinset → ℕ}
  {u v : V}
-- given
  (hnd : ∀ e ∈ S.edgeFinset, ¬ e.IsDiag)
  (huv : u ≠ v)
  (K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e})
  (hsrc : sources S (ofEdgeFun S (fun e => m e - K₂.1 e)) = {u, v}) :
-- imply
  connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) u v := by
-- proof
  apply StatMech.Walls.gc19_conn_of_sourcePair S m hnd huv K₂ hsrc

/--
[gc19_cert_of_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_cert_of_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  [Fintype V']
  [DecidableEq V']
  {G : SimpleGraph V'}
  [DecidableRel G.Adj]
  {o x y : V'}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V')) → (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) none) ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some x)) ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some y)) ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none} → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none) ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some x) none)) :
-- imply
  gc16_PerConfigCert G β h o x y := by
-- proof
  apply StatMech.Walls.gc19_cert_of_allConn S G β h o x y hox hoy hxy hall

/--
[gc19_ursell_nonpos_of_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean)
-/
@[path]
private lemma gc19_ursell_nonpos_of_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  [Fintype V']
  [DecidableEq V']
  {G : SimpleGraph V'}
  [DecidableRel G.Adj]
  {o x y : V'}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V')) → (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) none) ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some x)) ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some y)) ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none} → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none) ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some x) none)) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc19_ursell_nonpos_of_allConn S G β h o x y hox hoy hxy hall


-- created on 2026-10-23
