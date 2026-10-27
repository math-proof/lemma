import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc3_twosourceswitch
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc3_sources_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_twosourceswitch.lean)
-/
@[path]
private lemma gc3_sources_shift_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P Q : Finset ι}
  {A : Finset V}
-- given
  (hP : P ⊆ m)
  (hQ : Q ⊆ m) :
-- imply
  Set.BijOn (fun K => (K ∆ P) ∆ Q) {K | K ⊆ m ∧ sources ends K = A} {K | K ⊆ m ∧ sources ends K = A ∆ sources ends P ∆ sources ends Q} := by
-- proof
  apply StatMech.Walls.gc3_sources_shift ends m P Q hP hQ A

/--
[gc3_twoSourceSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_twosourceswitch.lean)
-/
@[path]
private lemma gc3_twoSourceSwitch_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v s t : V}
-- given
  (huv : u ≠ v)
  (hst : s ≠ t)
  (hconnuv : connK ends m u v)
  (hconnst : connK ends m s t) :
-- imply
  #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t})) = #(m.powerset.filter (fun K => sources ends K = A)) := by
-- proof
  apply StatMech.Walls.gc3_twoSourceSwitch ends m A huv hst hconnuv hconnst

/--
[gc3_twoSourceSwitch_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_twosourceswitch.lean)
-/
@[path]
private lemma gc3_twoSourceSwitch_lemma_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v s t : V}
  {F : Finset ι → ℝ}
-- given
  (huv : u ≠ v)
  (hst : s ≠ t)
  (hconnuv : connK ends m u v)
  (hconnst : connK ends m s t) :
-- imply
  ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}), F m = ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m := by
-- proof
  apply StatMech.Walls.gc3_twoSourceSwitch_lemma ends m A huv hst hconnuv hconnst F

/--
[gc3_twoSourceSwitch_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_twosourceswitch.lean)
-/
@[path]
private lemma gc3_twoSourceSwitch_current_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {M : Finset (Copy G m)}
  {A : Finset W}
  {u v s t : W}
-- given
  (huv : u ≠ v)
  (hst : s ≠ t)
  (hconnuv : connK (endsM G m) M u v)
  (hconnst : connK (endsM G m) M s t) :
-- imply
  #(M.powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v} ∆ {s, t})) = #(M.powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A)) := by
-- proof
  apply StatMech.Walls.gc3_twoSourceSwitch_current G m M A huv hst hconnuv hconnst

/--
[gc3_twoSourceSwitch_coincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_twosourceswitch.lean)
-/
@[path]
private lemma gc3_twoSourceSwitch_coincident_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V} :
-- imply
  #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {u, v})) = #(m.powerset.filter (fun K => sources ends K = A)) := by
-- proof
  apply StatMech.Walls.gc3_twoSourceSwitch_coincident ends m A u v


-- created on 2026-10-23
