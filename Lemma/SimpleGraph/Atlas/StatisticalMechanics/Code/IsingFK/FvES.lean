import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.IsingFK.FvES
open StatMech StatMech.IsingFK


/--
[sum_eval_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma sum_eval_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  [Fintype A]
  [DecidableEq A]
  [Fintype B]
  [DecidableEq B]
  {a₀ : A}
  {F : B → ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  (∑ g : A → B, F (g a₀)) = (Fintype.card ({a : A // a ≠ a₀} → B)) • (∑ b : B, F b) := by
-- proof
  apply StatMech.IsingFK.sum_eval_factor G bdry a₀ F

/--
[wiredColourEquiv_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma wiredColourEquiv_apply_val_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
  {ω : ConfigSpace (Sym2 V)}
  {v₀ : V}
  {x : V}
-- given
  (bdry : V → Prop)
  (hv₀ : bdry v₀)
  (σ : {σ : V → Fin q // ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ}) :
-- imply
  (wiredColourEquiv G bdry b ω v₀ hv₀ σ).1 ((wiredSub G bdry ω).connectedComponentMk x) = σ.1 x := by
-- proof
  apply StatMech.IsingFK.wiredColourEquiv_apply_val G bdry b ω v₀ hv₀ σ x

/--
[sum_isingSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma sum_isingSpin_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
-- given
  (bdry : V → Prop) :
-- imply
  (∑ b : Fin 2, isingSpin b) = 0 := by
-- proof
  apply StatMech.IsingFK.sum_isingSpin G bdry

/--
[connToBdry_iff_componentMk_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma connToBdry_iff_componentMk_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {v₀ : V}
  {ω : ConfigSpace (Sym2 V)}
  {x : V}
-- given
  (bdry : V → Prop)
  (hv₀ : bdry v₀) :
-- imply
  ConnToBdry G bdry ω x ↔ (wiredSub G bdry ω).connectedComponentMk x = (wiredSub G bdry ω).connectedComponentMk v₀ := by
-- proof
  apply StatMech.IsingFK.connToBdry_iff_componentMk_eq G bdry v₀ hv₀ ω x

/--
[card_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma card_pinned_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  [Fintype C]
  [DecidableEq C]
  {q : ℕ}
  {c₀ : C}
  {b : Fin q}
-- given
  (bdry : V → Prop) :
-- imply
  Fintype.card {τ : C → Fin q // τ c₀ = b} = q ^ (Fintype.card C - 1) := by
-- proof
  apply StatMech.IsingFK.card_pinned G bdry c₀ b

/--
[sum_pinned_eq_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma sum_pinned_eq_filter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  [Fintype C]
  [DecidableEq C]
  {c₀ : C}
  {F : (C → Fin 2) → ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  (∑ τ : {τ : C → Fin 2 // τ c₀ = 0}, F τ.1) = ∑ τ ∈ Finset.univ.filter (fun τ : C → Fin 2 => τ c₀ = 0), F τ := by
-- proof
  apply StatMech.IsingFK.sum_pinned_eq_filter G bdry c₀ F

/--
[colour_spin_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma colour_spin_cancel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  [Fintype C]
  [DecidableEq C]
  {c₀ cx : C}
-- given
  (bdry : V → Prop)
  (h : cx ≠ c₀) :
-- imply
  (∑ τ ∈ Finset.univ.filter (fun τ : C → Fin 2 => τ c₀ = 0), isingSpin (τ cx)) = 0 := by
-- proof
  apply StatMech.IsingFK.colour_spin_cancel G bdry c₀ cx h

/--
[colour_spin_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma colour_spin_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  [Fintype C]
  [DecidableEq C]
  {c₀ cx : C}
-- given
  (bdry : V → Prop)
  (h : cx = c₀) :
-- imply
  (∑ τ ∈ Finset.univ.filter (fun τ : C → Fin 2 => τ c₀ = 0), isingSpin (τ cx)) = (2 : ℝ) ^ (Fintype.card C - 1) := by
-- proof
  apply StatMech.IsingFK.colour_spin_const G bdry c₀ cx h

/--
[colour_spin_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma colour_spin_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {ω : ConfigSpace (Sym2 V)}
  {v₀ : V}
  {x : V}
-- given
  (bdry : V → Prop)
  (hv₀ : bdry v₀) :
-- imply
  (∑ σ ∈ Finset.univ.filter (fun σ : V → Fin 2 => ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry 0 σ), isingSpin (σ x)) = if ConnToBdry G bdry ω x then (2 : ℝ) ^ (Fintype.card (wiredSub G bdry ω).ConnectedComponent - 1) else 0 := by
-- proof
  apply StatMech.IsingFK.colour_spin_sum G bdry ω v₀ hv₀ x

/--
[numClustersBC_eq_card_wiredSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma numClustersBC_eq_card_wiredSub_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  numClustersBC G (boundaryCliqueGraph bdry) ω = Fintype.card (wiredSub G bdry ω).ConnectedComponent := by
-- proof
  apply StatMech.IsingFK.numClustersBC_eq_card_wiredSub G bdry ω

/--
[esWeightWired_spin_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma esWeightWired_spin_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {v₀ : V}
  {x : V}
-- given
  (bdry : V → Prop)
  (hv₀ : bdry v₀) :
-- imply
  (∑ σ : V → Fin 2, esWeightWired G bdry (0 : Fin 2) p σ ω * isingSpin (σ x)) = edgeProduct G p ω * (if ConnToBdry G bdry ω x then (2 : ℝ) ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1) else 0) := by
-- proof
  apply StatMech.IsingFK.esWeightWired_spin_sum G bdry p ω v₀ hv₀ x

/--
[one_le_numClustersBC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma one_le_numClustersBC_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {v₀ : V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω := by
-- proof
  apply StatMech.IsingFK.one_le_numClustersBC G bdry v₀ ω

/--
[edgeProduct_pow_eq_bcWeight_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma edgeProduct_pow_eq_bcWeight_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {v₀ : V}
-- given
  (bdry : V → Prop) :
-- imply
  (2 : ℝ) * (edgeProduct G p ω * (2 : ℝ) ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1)) = bcWeight G (boundaryCliqueGraph bdry) p (2 : ℝ) ω := by
-- proof
  apply StatMech.IsingFK.edgeProduct_pow_eq_bcWeight_half G bdry p ω v₀

/--
[esWiredOnePoint_eq_wiredConnToBdryProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma esWiredOnePoint_eq_wiredConnToBdryProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p : ℝ}
  {x : V}
  {v₀ : V}
-- given
  (bdry : V → Prop)
  (hv₀ : bdry v₀) :
-- imply
  esWiredOnePoint G bdry (0 : Fin 2) p x = wiredConnToBdryProb G bdry p x := by
-- proof
  apply StatMech.IsingFK.esWiredOnePoint_eq_wiredConnToBdryProb G bdry p x v₀ hv₀

/--
[wiredConnToBdryProb_eq_wiredFkProb_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean)
-/
@[path]
private lemma wiredConnToBdryProb_eq_wiredFkProb_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p : ℝ}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  wiredConnToBdryProb G bdry p x = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x), wiredFkProb G bdry p (2 : ℝ) ω := by
-- proof
  apply StatMech.IsingFK.wiredConnToBdryProb_eq_wiredFkProb_sum G bdry p x


-- created on 2026-10-23
