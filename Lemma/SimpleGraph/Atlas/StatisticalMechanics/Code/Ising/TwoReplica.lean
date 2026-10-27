import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
open Finset Classical StatMech StatMech.Ising


/--
[mem_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma mem_sources_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {n : Current V}
  {x : V} :
-- imply
  x ∈ sources E n ↔ Odd (incidentFlux E n x) := by
-- proof
  apply StatMech.Ising.mem_sources E

/--
[incidentFlux_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma incidentFlux_add_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {n m : Current V}
  {x : V} :
-- imply
  incidentFlux E (fun e => n e + m e) x = incidentFlux E n x + incidentFlux E m x := by
-- proof
  apply StatMech.Ising.incidentFlux_add E n m x

/--
[sources_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma sources_add_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {n m : Current V} :
-- imply
  sources E (fun e => n e + m e) = sources E n ∆ sources E m := by
-- proof
  apply StatMech.Ising.sources_add E n m

/--
[adjP_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma adjP_symm_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P : Finset (Sym2 V)}
  {a b : V} :
-- imply
  adjP P a b → adjP P b a := by
-- proof
  apply StatMech.Ising.adjP_symm E P

/--
[connP_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma connP_symm_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P : Finset (Sym2 V)}
  {a b : V} :
-- imply
  connP P a b → connP P b a := by
-- proof
  apply StatMech.Ising.connP_symm E P

/--
[connP_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma connP_mono_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P Q : Finset (Sym2 V)}
  {a b : V}
-- given
  (hPQ : P ⊆ Q)
  (h : connP P a b) :
-- imply
  connP Q a b := by
-- proof
  apply StatMech.Ising.connP_mono E hPQ h

/--
[oddEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma oddEdges_subset_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V} :
-- imply
  oddEdges E m ⊆ E := by
-- proof
  apply StatMech.Ising.oddEdges_subset E m

/--
[oddEdges_subset_posEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma oddEdges_subset_posEdges_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V} :
-- imply
  oddEdges E m ⊆ posEdges E m := by
-- proof
  apply StatMech.Ising.oddEdges_subset_posEdges E m

/--
[connOdd_imp_connPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma connOdd_imp_connPos_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {u v : V}
-- given
  (h : connP (oddEdges E m) u v) :
-- imply
  connP (posEdges E m) u v := by
-- proof
  apply StatMech.Ising.connOdd_imp_connPos E m h

/--
[mem_srcP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma mem_srcP_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P : Finset (Sym2 V)}
  {x : V} :
-- imply
  x ∈ srcP P ↔ Odd (degP P x) := by
-- proof
  apply StatMech.Ising.mem_srcP E

/--
[mem_compOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma mem_compOf_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P : Finset (Sym2 V)}
  {u x : V} :
-- imply
  x ∈ compOf P u ↔ connP P u x := by
-- proof
  apply StatMech.Ising.mem_compOf E

/--
[comp_edge_card_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma comp_edge_card_even_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P : Finset (Sym2 V)}
  {u : V}
  {e : Sym2 V}
-- given
  (hnd : ∀ e ∈ P, ¬ e.IsDiag)
  (he : e ∈ P) :
-- imply
  Even (#((compOf P u).filter (fun x => x ∈ e))) := by
-- proof
  apply StatMech.Ising.comp_edge_card_even E P hnd u he

/--
[sum_deg_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma sum_deg_comp_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P : Finset (Sym2 V)}
  {u : V} :
-- imply
  ∑ x ∈ compOf P u, degP P x = ∑ e ∈ P, #((compOf P u).filter (fun x => x ∈ e)) := by
-- proof
  apply StatMech.Ising.sum_deg_comp_eq E P u

/--
[sum_deg_comp_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma sum_deg_comp_even_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P : Finset (Sym2 V)}
  {u : V}
-- given
  (hnd : ∀ e ∈ P, ¬ e.IsDiag) :
-- imply
  Even (∑ x ∈ compOf P u, degP P x) := by
-- proof
  apply StatMech.Ising.sum_deg_comp_even E P hnd u

/--
[even_sum_iff_even_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma even_sum_iff_even_count_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {s : Finset α}
  {f : α → ℕ} :
-- imply
  Even (∑ x ∈ s, f x) ↔ Even (#(s.filter (fun x => Odd (f x)))) := by
-- proof
  apply StatMech.Ising.even_sum_iff_even_count E s f

/--
[path_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma path_exists_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P : Finset (Sym2 V)}
  {u v : V}
-- given
  (hnd : ∀ e ∈ P, ¬ e.IsDiag)
  (hu_odd : Odd (degP P u))
  (hbdry : ∀ x, Odd (degP P x) → x = u ∨ x = v)
  (huv : u ≠ v) :
-- imply
  connP P u v := by
-- proof
  apply StatMech.Ising.path_exists E P hnd u v hu_odd hbdry huv

/--
[card_filter_zmod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma card_filter_zmod_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  [DecidableEq α]
  [Fintype α]
  {T : Finset α}
  [DecidablePred p]
-- given
  (p : α → Prop) :
-- imply
  ((#(T.filter p) : ℕ) : ZMod 2) = ∑ i : α, (if i ∈ T then (1 : ZMod 2) else 0) * (if p i then (1 : ZMod 2) else 0) := by
-- proof
  apply StatMech.Ising.card_filter_zmod E T p

/--
[odd_degP_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma odd_degP_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {S T : Finset (Sym2 V)}
  {x : V} :
-- imply
  Odd (degP (S ∆ T) x) ↔ (Odd (degP S x) ≠ Odd (degP T x)) := by
-- proof
  apply StatMech.Ising.odd_degP_symmDiff E S T x

/--
[srcP_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma srcP_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {S T : Finset (Sym2 V)} :
-- imply
  srcP (S ∆ T) = srcP S ∆ srcP T := by
-- proof
  apply StatMech.Ising.srcP_symmDiff E S T

/--
[srcP_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma srcP_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {e : Sym2 V}
  {a b : V}
-- given
  (hab : e = s(a, b))
  (hne : a ≠ b) :
-- imply
  srcP ({e} : Finset (Sym2 V)) = {a, b} := by
-- proof
  apply StatMech.Ising.srcP_singleton E e a b hab hne

/--
[exists_conn_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma exists_conn_set_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P₀ : Finset (Sym2 V)}
  {u v : V}
-- given
  (hconn : connP P₀ u v)
  (huv : u ≠ v) :
-- imply
  ∃ P ⊆ P₀, srcP P = {u, v} := by
-- proof
  apply StatMech.Ising.exists_conn_set E P₀ hconn huv

/--
[srcP_oddEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma srcP_oddEdges_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V} :
-- imply
  srcP (oddEdges E m) = sources E m := by
-- proof
  apply StatMech.Ising.srcP_oddEdges E m

/--
[reflect_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma reflect_apply_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V}
  {e : Sym2 V} :
-- imply
  reflect m P n e = if e ∈ P then m e - n e else n e := by
-- proof
  apply StatMech.Ising.reflect_apply E m P n e

/--
[reflect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma reflect_le_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V}
-- given
  (hn : ∀ e, n e ≤ m e) :
-- imply
  ∀ e, reflect m P n e ≤ m e := by
-- proof
  apply StatMech.Ising.reflect_le E m P hn

/--
[reflect_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma reflect_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V}
-- given
  (hn : ∀ e, n e ≤ m e) :
-- imply
  reflect m P (reflect m P n) = n := by
-- proof
  apply StatMech.Ising.reflect_involutive E m P hn

/--
[reflect_add_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma reflect_add_complement_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V}
  {e : Sym2 V}
-- given
  (hn : ∀ e, n e ≤ m e) :
-- imply
  reflect m P n e + reflect m P (fun e => m e - n e) e = m e := by
-- proof
  apply StatMech.Ising.reflect_add_complement E m P hn e

/--
[reflect_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma reflect_complement_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V} :
-- imply
  (fun e => m e - reflect m P n e) = reflect m P (fun e => m e - n e) := by
-- proof
  apply StatMech.Ising.reflect_complement E m P n

/--
[reflect_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma reflect_parity_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V}
  {e : Sym2 V}
-- given
  (hn : ∀ e, n e ≤ m e)
  (hodd : ∀ e ∈ P, Odd (m e)) :
-- imply
  ((reflect m P n e : ℕ) : ZMod 2) = (n e : ZMod 2) + (if e ∈ P then 1 else 0) := by
-- proof
  apply StatMech.Ising.reflect_parity E m P n hn hodd e

/--
[degP_as_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma degP_as_sum_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {P : Finset (Sym2 V)}
  {x : V}
-- given
  (hP : P ⊆ E) :
-- imply
  degP P x = ∑ e ∈ E.filter (fun e => x ∈ e), (if e ∈ P then 1 else 0) := by
-- proof
  apply StatMech.Ising.degP_as_sum E P hP x

/--
[flux_reflect_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma flux_reflect_parity_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V}
  {x : V}
-- given
  (hn : ∀ e, n e ≤ m e)
  (hP : P ⊆ E)
  (hodd : ∀ e ∈ P, Odd (m e)) :
-- imply
  ((incidentFlux E (reflect m P n) x : ℕ) : ZMod 2) = ((incidentFlux E n x : ℕ) : ZMod 2) + ((degP P x : ℕ) : ZMod 2) := by
-- proof
  apply StatMech.Ising.flux_reflect_parity E m P n hn hP hodd x

/--
[sources_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma sources_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V}
-- given
  (hn : ∀ e, n e ≤ m e)
  (hP : P ⊆ E)
  (hodd : ∀ e ∈ P, Odd (m e)) :
-- imply
  sources E (reflect m P n) = sources E n ∆ srcP P := by
-- proof
  apply StatMech.Ising.sources_reflect E m P n hn hP hodd

/--
[reflect_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma reflect_bijOn_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {A : Finset V}
-- given
  (hP : P ⊆ E)
  (hodd : ∀ e ∈ P, Odd (m e)) :
-- imply
  Set.BijOn (reflect m P) {n | (∀ e, n e ≤ m e) ∧ sources E n = A} {n | (∀ e, n e ≤ m e) ∧ sources E n = A ∆ srcP P} := by
-- proof
  apply StatMech.Ising.reflect_bijOn E m P hP hodd A

/--
[connOdd_of_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma connOdd_of_sources_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {u v : V}
-- given
  (hnd : ∀ e ∈ E, ¬ e.IsDiag)
  (huv : u ≠ v)
  (hsrc : sources E m = {u, v}) :
-- imply
  connP (oddEdges E m) u v := by
-- proof
  apply StatMech.Ising.connOdd_of_sources E m hnd huv hsrc

/--
[ising_switching_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma ising_switching_lemma_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {u v : V}
  {A : Finset V}
-- given
  (huv : u ≠ v)
  (hconn : connP (oddEdges E m) u v) :
-- imply
  Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A ∆ {u, v}} = Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A} := by
-- proof
  apply StatMech.Ising.ising_switching_lemma E m huv hconn A

/--
[ising_switching_lemma_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma ising_switching_lemma_pair_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {n₁ n₂ : Current V}
  {u v : V}
  {A : Finset V}
-- given
  (huv : u ≠ v)
  (hconn : connP (oddEdges E (fun e => n₁ e + n₂ e)) u v) :
-- imply
  Nat.card {n : Current V // (∀ e, n e ≤ n₁ e + n₂ e) ∧ sources E n = A ∆ {u, v}} = Nat.card {n : Current V // (∀ e, n e ≤ n₁ e + n₂ e) ∧ sources E n = A} := by
-- proof
  apply StatMech.Ising.ising_switching_lemma_pair E n₁ n₂ huv hconn A

/--
[ising_switching_sourceless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean)
-/
@[path]
private lemma ising_switching_sourceless_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {u v : V}
-- given
  (hnd : ∀ e ∈ E, ¬ e.IsDiag)
  (huv : u ≠ v)
  (hsrc : sources E m = {u, v}) :
-- imply
  Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = {u, v}} = Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = ∅} := by
-- proof
  apply StatMech.Ising.ising_switching_sourceless E m hnd huv hsrc


-- created on 2026-10-23
