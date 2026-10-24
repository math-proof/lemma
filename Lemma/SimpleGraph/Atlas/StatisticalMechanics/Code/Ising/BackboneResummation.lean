import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.BackboneResummation
open Finset Classical StatMech StatMech.Ising


/--
[bbr_restrict_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_restrict_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  [DecidablePred p]
  {e : Sym2 V}
-- given
  (p : Sym2 V → Prop) :
-- imply
  restrictCut n p e ≤ n e := by
-- proof
  apply StatMech.Ising.bbr_restrict_le G n p e

/--
[bbr_cut_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_cut_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  [DecidablePred p]
-- given
  (p : Sym2 V → Prop) :
-- imply
  (fun e => restrictCut n p e + restrictCut n (fun e => ¬ p e) e) = n := by
-- proof
  apply StatMech.Ising.bbr_cut_split G n p

/--
[bbr_weight_cut_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_weight_cut_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n : Current V}
  [DecidablePred p]
-- given
  (p : Sym2 V → Prop) :
-- imply
  Sharpness.weight G β J n = Sharpness.weight G β J (restrictCut n p) * Sharpness.weight G β J (restrictCut n (fun e => ¬ p e)) := by
-- proof
  apply StatMech.Ising.bbr_weight_cut_factor G β J n p

/--
[bbr_sources_cut_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_sources_cut_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  [DecidablePred p]
-- given
  (p : Sym2 V → Prop) :
-- imply
  Sharpness.sources G n = Sharpness.sources G (restrictCut n p) ∆ Sharpness.sources G (restrictCut n (fun e => ¬ p e)) := by
-- proof
  apply StatMech.Ising.bbr_sources_cut_split G n p

/--
[bbr_mass_eq_weight_mul_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_mass_eq_weight_mul_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V} :
-- imply
  hnw_mass G β J m A = Sharpness.weight G β J m * ∑ K : {K : Current V // ∀ e, K e ≤ m e}, (if Sharpness.sources G K.1 = A then (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (K.1 e) : ℝ)) else 0) := by
-- proof
  apply StatMech.Ising.bbr_mass_eq_weight_mul_count G β J m A

/--
[bbr_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_mass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {S : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ hnw_mass G β J m S := by
-- proof
  apply StatMech.Ising.bbr_mass_nonneg G β J hβ hJ m S

/--
[bbr_inj_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_inj_domination_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq α]
  [DecidableEq β]
  {S : Finset α}
  {T : Finset β}
  {f : α → ℝ}
  {g : β → ℝ}
  {Ψ : α → β}
-- given
  (hΨmem : ∀ a ∈ S, Ψ a ∈ T)
  (hΨinj : ∀ a ∈ S, ∀ a' ∈ S, Ψ a = Ψ a' → a = a')
  (hgnn : ∀ b ∈ T, 0 ≤ g b)
  (hbound : ∀ a ∈ S, 2 * f a ≤ g (Ψ a)) :
-- imply
  2 * (∑ a ∈ S, f a) ≤ ∑ b ∈ T, g b := by
-- proof
  apply StatMech.Ising.bbr_inj_domination G S T f g Ψ hΨmem hΨinj hgnn hbound

/--
[bbr_surgery_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_surgery_satisfiable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hno : bbr_allFilter G M o x y = ∅) :
-- imply
  bbr_BackboneSurgery G β J M A o x y := by
-- proof
  apply StatMech.Ising.bbr_surgery_satisfiable G β J M A o x y hno

/--
[bbr_hdom_of_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_hdom_of_surgery_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hsurg : bbr_BackboneSurgery G β J M A o x y) :
-- imply
  2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.bbr_hdom_of_surgery G β J hβ hJ M A o x y hsurg

/--
[bbr_closure_of_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_closure_of_surgery_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
  (hsurg : bbr_BackboneSurgery G β J M A o x y) :
-- imply
  0 ≤ ∑ m ∈ M, hnw_gap G β J m A o x y := by
-- proof
  apply StatMech.Ising.bbr_closure_of_surgery G β J hβ hJ M hnd A hm hox hoy hxy hcoh hsurg

/--
[bbr_ghs_of_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean)
-/
@[path]
private lemma bbr_ghs_of_surgery_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
  (hsurg : bbr_BackboneSurgery G β J M A o x y) :
-- imply
  (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y})) + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y})) + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x})) ≤ ∑ m ∈ M, hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.bbr_ghs_of_surgery G β J hβ hJ M hnd A hm hox hoy hxy hcoh hsurg


-- created on 2026-10-23
