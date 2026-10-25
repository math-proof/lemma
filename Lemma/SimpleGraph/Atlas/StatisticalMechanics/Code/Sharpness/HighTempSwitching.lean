import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
open Finset StatMech StatMech.Sharpness


/--
[hasOddBoundary_iff_srcP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma hasOddBoundary_iff_srcP_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {A : Finset V} :
-- imply
  HasOddBoundary F A ↔ srcP F = A := by
-- proof
  apply StatMech.Sharpness.hasOddBoundary_iff_srcP F A

/--
[hasOddBoundary_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma hasOddBoundary_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {F H : Finset (Sym2 V)}
  {A B : Finset V}
-- given
  (hF : HasOddBoundary F A)
  (hH : HasOddBoundary H B) :
-- imply
  HasOddBoundary (F ∆ H) (A ∆ B) := by
-- proof
  apply StatMech.Sharpness.hasOddBoundary_symmDiff hF hH

/--
[mem_symmDiff_singleton_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma mem_symmDiff_singleton_iff_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq α]
  {S : Finset α}
  {a x : α} :
-- imply
  x ∈ S ∆ {a} ↔ (x ∈ S ↔ x ≠ a) := by
-- proof
  apply StatMech.Sharpness.mem_symmDiff_singleton_iff S a x

/--
[card_pair_symmDiff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma card_pair_symmDiff_singleton_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq α]
  {F H : Finset α}
  {e : α}
-- given
  (he : e ∈ F ∆ H) :
-- imply
  (F ∆ {e}).card + (H ∆ {e}).card = F.card + H.card := by
-- proof
  apply StatMech.Sharpness.card_pair_symmDiff_singleton F H he

/--
[card_pair_symmDiff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma card_pair_symmDiff_eq_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq α]
  {F H Q : Finset α}
-- given
  (hQ : Q ⊆ F ∆ H) :
-- imply
  (F ∆ Q).card + (H ∆ Q).card = F.card + H.card := by
-- proof
  apply StatMech.Sharpness.card_pair_symmDiff_eq F H Q hQ

/--
[sourcePair_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma sourcePair_self_eq
  [Fintype V]
  [DecidableEq V]
  {a : V} :
-- imply
  sourcePair a a = ∅ := by
-- proof
  apply StatMech.Sharpness.sourcePair_self a

/--
[sourcePair_eq_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma sourcePair_eq_pair_eq
  [Fintype V]
  [DecidableEq V]
  {a b : V}
-- given
  (hab : a ≠ b) :
-- imply
  sourcePair a b = {a, b} := by
-- proof
  apply StatMech.Sharpness.sourcePair_eq_pair hab

/--
[sourcePair_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma sourcePair_chain_eq
  [Fintype V]
  [DecidableEq V]
  {a b c d : V} :
-- imply
  sourcePair a b ∆ sourcePair b c ∆ sourcePair c d = sourcePair a d := by
-- proof
  apply StatMech.Sharpness.sourcePair_chain a b c d

/--
[hasOddBoundary_path_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma hasOddBoundary_path_edges_eq
  [Fintype V]
  [DecidableEq V]
  {K : SimpleGraph V}
  {a b : V}
  {p : K.Walk a b}
-- given
  (hp : p.IsPath) :
-- imply
  HasOddBoundary p.edges.toFinset (sourcePair a b) := by
-- proof
  apply StatMech.Sharpness.hasOddBoundary_path_edges p hp

/--
[sourcePair_symmDiff_firstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma sourcePair_symmDiff_firstExit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F H : Finset (Sym2 V)}
  {o z : V}
  {S : Finset V}
-- given
  (hFsub : F ⊆ G.edgeFinset)
  (hHsub : H ⊆ G.edgeFinset)
  (hoz : o ≠ z)
  (hF : HasOddBoundary F (sourcePair o z))
  (hH : HasOddBoundary H ∅)
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  ∃ x ∈ S, ∃ y ∉ S, ∃ Q : Finset (Sym2 V), Q ⊆ F ∆ H ∧ HasOddBoundary Q (sourcePair o x) ∧ s(x, y) ∉ Q ∧ s(x, y) ∈ F ∆ H := by
-- proof
  apply StatMech.Sharpness.sourcePair_symmDiff_firstExit G F H hFsub hHsub hoz hF hH S ho hz

/--
[erase_eq_symmDiff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma erase_eq_symmDiff_singleton_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq α]
  {F : Finset α}
  {e : α}
-- given
  (he : e ∈ F) :
-- imply
  F.erase e = F ∆ {e} := by
-- proof
  apply StatMech.Sharpness.erase_eq_symmDiff_singleton F he

/--
[card_switch_erase_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma card_switch_erase_exit_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq α]
  {F H Q : Finset α}
  {e : α}
-- given
  (hQ : Q ⊆ F ∆ H)
  (heF : e ∈ F)
  (heQ : e ∉ Q) :
-- imply
  (H ∆ Q).card + ((F ∆ Q).erase e).card + 1 = F.card + H.card := by
-- proof
  apply StatMech.Sharpness.card_switch_erase_exit F H Q hQ heF heQ

/--
[hasOddBoundary_singleton_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma hasOddBoundary_singleton_sourcePair_eq
  [Fintype V]
  [DecidableEq V]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  HasOddBoundary ({s(x, y)} : Finset (Sym2 V)) (sourcePair x y) := by
-- proof
  apply StatMech.Sharpness.hasOddBoundary_singleton_sourcePair hxy

/--
[hasOddBoundary_switch_erase_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma hasOddBoundary_switch_erase_exit_eq
  [Fintype V]
  [DecidableEq V]
  {F H Q : Finset (Sym2 V)}
  {o x y z : V}
-- given
  (hF : HasOddBoundary F (sourcePair o z))
  (hH : HasOddBoundary H ∅)
  (hQ : HasOddBoundary Q (sourcePair o x))
  (hxy : x ≠ y)
  (heF : s(x, y) ∈ F)
  (heQ : s(x, y) ∉ Q) :
-- imply
  HasOddBoundary (H ∆ Q) (sourcePair o x) ∧ HasOddBoundary ((F ∆ Q).erase s(x, y)) (sourcePair y z) := by
-- proof
  apply StatMech.Sharpness.hasOddBoundary_switch_erase_exit hF hH hQ hxy heF heQ

/--
[exists_highTempFirstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma exists_highTempFirstExit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Finset (Sym2 V)}
  {o z : V}
  {S : Finset V}
-- given
  (hK : K ⊆ G.edgeFinset)
  (hbd : HasOddBoundary K (sourcePair o z))
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  Nonempty (HighTempFirstExit K o z S) := by
-- proof
  apply StatMech.Sharpness.exists_highTempFirstExit G K hK hbd S ho hz

/--
[highTempFirstExit_Q_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma highTempFirstExit_Q_congr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K L : Finset (Sym2 V)}
  {o z : V}
  {S : Finset V}
-- given
  (hKL : K = L)
  (hK : K ⊆ G.edgeFinset)
  (hL : L ⊆ G.edgeFinset)
  (hbdK : HasOddBoundary K (sourcePair o z))
  (hbdL : HasOddBoundary L (sourcePair o z))
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  (highTempFirstExit G K hK hbdK S ho hz).Q = (highTempFirstExit G L hL hbdL S ho hz).Q := by
-- proof
  apply StatMech.Sharpness.highTempFirstExit_Q_congr G hKL hK hL hbdK hbdL S ho hz

/--
[prod_pair_symmDiff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma prod_pair_symmDiff_eq_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq α]
  {t : α → ℝ}
  {F H Q : Finset α}
-- given
  (hQ : Q ⊆ F ∆ H) :
-- imply
  (∏ e ∈ F ∆ Q, t e) * (∏ e ∈ H ∆ Q, t e) = (∏ e ∈ F, t e) * (∏ e ∈ H, t e) := by
-- proof
  apply StatMech.Sharpness.prod_pair_symmDiff_eq t F H Q hQ

/--
[prod_switch_erase_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean)
-/
@[path]
private lemma prod_switch_erase_exit_eq
  [Fintype V]
  [DecidableEq V]
  {t : Sym2 V → ℝ}
  {F H Q : Finset (Sym2 V)}
  {x y : V}
-- given
  (hQ : Q ⊆ F ∆ H)
  (heF : s(x, y) ∈ F)
  (heQ : s(x, y) ∉ Q) :
-- imply
  (∏ e ∈ H ∆ Q, t e) * t s(x, y) * (∏ e ∈ (F ∆ Q).erase s(x, y), t e) = (∏ e ∈ F, t e) * (∏ e ∈ H, t e) := by
-- proof
  apply StatMech.Sharpness.prod_switch_erase_exit t F H Q hQ heF heQ


-- created on 2026-10-23
