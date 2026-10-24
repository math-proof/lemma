import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc32surgery
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc32_switch_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc32surgery.lean)
-/
@[path]
private lemma gc32_switch_card_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : RandomCurrent.sources ends m = A)
  (huv : u ≠ v)
  (hconn : RandomCurrent.connK ends m u v) :
-- imply
  #(m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {u, v})) = #(m.powerset.filter (fun K => RandomCurrent.sources ends K = A)) := by
-- proof
  apply StatMech.Walls.gc32_switch_card_eq G ends m hnd A hm huv hconn

/--
[gc32_switch_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc32surgery.lean)
-/
@[path]
private lemma gc32_switch_bijOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P : Finset ι}
  {u v : V}
  {A : Finset V}
-- given
  (hP : P ⊆ m)
  (hPsrc : RandomCurrent.sources ends P = {u, v}) :
-- imply
  Set.BijOn (fun K => K ∆ P) {K | K ⊆ m ∧ RandomCurrent.sources ends K = A} {K | K ⊆ m ∧ RandomCurrent.sources ends K = A ∆ {u, v}} := by
-- proof
  apply StatMech.Walls.gc32_switch_bijOn G ends m P hP hPsrc A

/--
[gc32_switch_card_disc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc32surgery.lean)
-/
@[path]
private lemma gc32_switch_card_disc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : RandomCurrent.sources ends m = A)
  (huv : u ≠ v)
  (hdisc : ¬ RandomCurrent.connK ends m u v) :
-- imply
  #(m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {u, v})) = 0 := by
-- proof
  apply StatMech.Walls.gc32_switch_card_disc G ends m hnd A hm huv hdisc

/--
[gc32_split_weight_cut_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc32surgery.lean)
-/
@[path]
private lemma gc32_split_weight_cut_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m n : Sharpness.Current V}
  [DecidablePred p]
-- given
  (p : Sym2 V → Prop) :
-- imply
  Sharpness.weight G β J n * Sharpness.weight G β J (fun e => m e - n e) = (Sharpness.weight G β J (StatMech.Ising.restrictCut n p) * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - n e) p)) * (Sharpness.weight G β J (StatMech.Ising.restrictCut n (fun e => ¬ p e)) * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - n e) (fun e => ¬ p e))) := by
-- proof
  apply StatMech.Walls.gc32_split_weight_cut_factor G β J m n p

/--
[gc32_sources_cut_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc32surgery.lean)
-/
@[path]
private lemma gc32_sources_cut_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {n : Sharpness.Current V}
  [DecidablePred p]
-- given
  (p : Sym2 V → Prop) :
-- imply
  Sharpness.sources G n = Sharpness.sources G (StatMech.Ising.restrictCut n p) ∆ Sharpness.sources G (StatMech.Ising.restrictCut n (fun e => ¬ p e)) := by
-- proof
  apply StatMech.Walls.gc32_sources_cut_split G n p

/--
[gc32_massDoubling_forces_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc32surgery.lean)
-/
@[path]
private lemma gc32_massDoubling_forces_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m m' : Sharpness.Current V}
  {B : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (htarget : hnw_mass G β J m' B = 0)
  (hdoub : 2 * hnw_mass G β J m B ≤ hnw_mass G β J m' B) :
-- imply
  hnw_mass G β J m B = 0 := by
-- proof
  apply StatMech.Walls.gc32_massDoubling_forces_zero G β J hβ hJ m m' B htarget hdoub

/--
[gc32_massDoubling_unsat_of_zero_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc32surgery.lean)
-/
@[path]
private lemma gc32_massDoubling_unsat_of_zero_targets_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
  {ma : Sharpness.Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hma : ma ∈ bbr_allFilter G M o x y)
  (hpos : 0 < hnw_mass G β J ma B)
  (hzero : ∀ m' ∈ bbr_noneFilter G M o x y, hnw_mass G β J m' B = 0) :
-- imply
  ¬ gc31_MassDoublingSurgery G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc32_massDoubling_unsat_of_zero_targets G β J hβ hJ M B o x y ma hma hpos hzero

/--
[gc32_gap_nonneg_of_massDoubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc32surgery.lean)
-/
@[path]
private lemma gc32_gap_nonneg_of_massDoubling_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = B)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
  (h : gc31_MassDoublingSurgery G β J M B o x y) :
-- imply
  0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y := by
-- proof
  apply StatMech.Walls.gc32_gap_nonneg_of_massDoubling G β J hβ hJ M hnd B hm hox hoy hxy hcoh h


-- created on 2026-10-23
