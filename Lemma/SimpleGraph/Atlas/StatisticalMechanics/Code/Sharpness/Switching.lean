import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
open Finset BigOperators Classical StatMech StatMech.Sharpness StatMech.Sharpness.RandomCurrent


/--
[mem_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma mem_sources_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {T : Finset ι}
  {x : V} :
-- imply
  x ∈ sources ends T ↔ Odd (degK ends T x) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.mem_sources

/--
[adjStep_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma adjStep_symm_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {a b : V} :
-- imply
  adjStep ends K a b → adjStep ends K b a := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.adjStep_symm ends K

/--
[connK_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma connK_symm_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {a b : V} :
-- imply
  connK ends K a b → connK ends K b a := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.connK_symm ends K

/--
[mem_compOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma mem_compOf_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {u x : V} :
-- imply
  x ∈ compOf ends K u ↔ connK ends K u x := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.mem_compOf

/--
[card_filter_zmod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma card_filter_zmod_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [DecidableEq α]
  [Fintype α]
  {T : Finset α}
  [DecidablePred p]
-- given
  (p : α → Prop) :
-- imply
  ((#(T.filter p) : ℕ) : ZMod 2) = ∑ i : α, (if i ∈ T then (1 : ZMod 2) else 0) * (if p i then (1 : ZMod 2) else 0) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.card_filter_zmod T p

/--
[odd_degK_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma odd_degK_symmDiff_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {S T : Finset ι}
  {x : V} :
-- imply
  Odd (degK ends (S ∆ T) x) ↔ (Odd (degK ends S x) ≠ Odd (degK ends T x)) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.odd_degK_symmDiff ends S T x

/--
[sources_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma sources_symmDiff_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {S T : Finset ι} :
-- imply
  sources ends (S ∆ T) = sources ends S ∆ sources ends T := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.sources_symmDiff ends S T

/--
[comp_edge_card_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma comp_edge_card_even_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {u : V}
  {i : ι}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hi : i ∈ K) :
-- imply
  Even (#((compOf ends K u).filter (fun x => x ∈ ends i))) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.comp_edge_card_even ends K hnd u hi

/--
[sum_deg_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma sum_deg_comp_eq_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {u : V} :
-- imply
  ∑ x ∈ compOf ends K u, degK ends K x = ∑ i ∈ K, #((compOf ends K u).filter (fun x => x ∈ ends i)) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.sum_deg_comp_eq ends K u

/--
[sum_deg_comp_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma sum_deg_comp_even_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {u : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) :
-- imply
  Even (∑ x ∈ compOf ends K u, degK ends K x) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.sum_deg_comp_even ends K hnd u

/--
[even_sum_iff_even_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma even_sum_iff_even_count_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {s : Finset α}
  {f : α → ℕ} :
-- imply
  Even (∑ x ∈ s, f x) ↔ Even (#(s.filter (fun x => Odd (f x)))) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.even_sum_iff_even_count s f

/--
[path_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma path_exists_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {u v : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hu_odd : Odd (degK ends K u))
  (hbdry : ∀ x, Odd (degK ends K x) → x = u ∨ x = v)
  (huv : u ≠ v) :
-- imply
  connK ends K u v := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.path_exists ends K hnd u v hu_odd hbdry huv

/--
[sources_shift_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma sources_shift_bijOn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P : Finset ι}
  {A : Finset V}
-- given
  (hP : P ⊆ m) :
-- imply
  Set.BijOn (fun K => K ∆ P) {K | K ⊆ m ∧ sources ends K = A} {K | K ⊆ m ∧ sources ends K = A ∆ sources ends P} := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.sources_shift_bijOn ends m P hP A

/--
[exists_conn_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma exists_conn_set_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {u v : V}
-- given
  (hconn : connK ends m u v)
  (huv : u ≠ v) :
-- imply
  ∃ P ⊆ m, sources ends P = {u, v} := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.exists_conn_set ends m hconn huv

/--
[switching_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma switching_card_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v) :
-- imply
  #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v})) = (if connK ends m u v then #(m.powerset.filter (fun K => sources ends K = A)) else 0) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.switching_card ends m hnd A hm huv

/--
[switching_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean)
-/
@[path]
private lemma switching_lemma_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
  {F : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v) :
-- imply
  ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), F m = ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m * (if connK ends m u v then 1 else 0) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.switching_lemma ends m hnd A hm huv F


-- created on 2026-10-23
