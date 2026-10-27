import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc93borbitcount
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc93b_pairAction_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_pairAction_involutive_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {τ : Equiv.Perm ι}
-- given
  (hτ2 : ∀ i, τ (τ i) = i) :
-- imply
  Function.Involutive (gc92b_pairAction (ι := ι) τ) := by
-- proof
  apply StatMech.Walls.gc93b_pairAction_involutive τ hτ2

/--
[gc93b_even_card_ff_involution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_even_card_ff_involution_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [DecidableEq α]
  {φ : α → α}
-- given
  (hinv : Function.Involutive φ) :
-- imply
  ∀ t : Finset α, (∀ a ∈ t, φ a ∈ t) → (∀ a ∈ t, φ a ≠ a) → Even t.card := by
-- proof
  apply StatMech.Walls.gc93b_even_card_ff_involution φ hinv

/--
[gc93b_even_nonfixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_even_nonfixed_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [DecidableEq α]
  {φ : α → α}
  {s : Finset α}
-- given
  (hinv : Function.Involutive φ)
  (hmap : ∀ a ∈ s, φ a ∈ s) :
-- imply
  Even (#(s.filter (fun a => φ a ≠ a))) := by
-- proof
  apply StatMech.Walls.gc93b_even_nonfixed φ hinv s hmap

/--
[gc93b_card_eq_fixed_add_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_card_eq_fixed_add_even_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [DecidableEq α]
  {φ : α → α}
  {s : Finset α}
-- given
  (hinv : Function.Involutive φ)
  (hmap : ∀ a ∈ s, φ a ∈ s) :
-- imply
  #s = #(s.filter (fun a => φ a = a)) + #(s.filter (fun a => φ a ≠ a)) ∧ Even (#(s.filter (fun a => φ a ≠ a))) := by
-- proof
  apply StatMech.Walls.gc93b_card_eq_fixed_add_even φ hinv s hmap

/--
[gc93b_two_mul_orbits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_two_mul_orbits_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [DecidableEq α]
  {φ : α → α}
  {s : Finset α}
-- given
  (hinv : Function.Involutive φ)
  (hmap : ∀ a ∈ s, φ a ∈ s) :
-- imply
  2 * (#(s.filter (fun a => φ a = a)) + #(s.filter (fun a => φ a ≠ a)) / 2) = #s + #(s.filter (fun a => φ a = a)) := by
-- proof
  apply StatMech.Walls.gc93b_two_mul_orbits φ hinv s hmap

/--
[gc93b_pairAction_fixed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_pairAction_fixed_iff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {τ : Equiv.Perm ι}
  {K₁ K₂ : Finset ι} :
-- imply
  gc92b_pairAction τ (K₁, K₂) = (K₁, K₂) ↔ K₁.image τ = K₁ ∧ K₂.image τ = K₂ := by
-- proof
  apply StatMech.Walls.gc93b_pairAction_fixed_iff τ K₁ K₂

/--
[gc93b_cogxg_fixed_eq_invariant_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_cogxg_fixed_eq_invariant_pairs_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x g : W}
  {τ : Equiv.Perm ι} :
-- imply
  #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s)) = #((gc91b_cogxgPairs ends m o x g).filter (fun s => s.1.image τ = s.1 ∧ s.2.image τ = s.2)) := by
-- proof
  apply StatMech.Walls.gc93b_cogxg_fixed_eq_invariant_pairs ends m o x g τ

/--
[gc93b_T3_fixed_eq_invariant_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_T3_fixed_eq_invariant_pairs_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {τ : Equiv.Perm ι} :
-- imply
  #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s = s)) = #((gc91b_T3Pairs ends m o x y g).filter (fun s => s.1.image τ = s.1 ∧ s.2.image τ = s.2)) := by
-- proof
  apply StatMech.Walls.gc93b_T3_fixed_eq_invariant_pairs ends m o x y g τ

/--
[gc93b_orbitcount_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_orbitcount_iff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {τ : Equiv.Perm ι}
-- given
  (hτ : ∀ i, ends (τ i) = ends i)
  (hτ2 : ∀ i, τ (τ i) = i)
  (hm : m.image τ = m) :
-- imply
  let cog := #(gc91b_cogxgPairs ends m o x g) let t3 := #(gc91b_T3Pairs ends m o x y g) let Fc := #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s)) let Ft := #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s = s)) let ncog := Fc + #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s ≠ s)) / 2 let nt3 := Ft + #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s ≠ s)) / 2 2 * ncog = cog + Fc ∧ 2 * nt3 = t3 + Ft ∧ (ncog ≤ nt3 ↔ cog + Fc ≤ t3 + Ft) := by
-- proof
  apply StatMech.Walls.gc93b_orbitcount_iff ends m τ hτ hτ2 hm

/--
[gc93b_wred_swap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_wred_swap_involutive_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  ∀ i : Fin 4, (Equiv.swap (1 : Fin 4) 2) ((Equiv.swap (1 : Fin 4) 2) i) = i := by
-- proof
  apply StatMech.Walls.gc93b_wred_swap_involutive

/--
[gc93b_wred_orbit_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_wred_orbit_data_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ≠ (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) = (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ≠ (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4))) = ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4))) = ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4))) := by
-- proof
  apply StatMech.Walls.gc93b_wred_orbit_data

/--
[gc93b_burnside_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_burnside_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {τ : Equiv.Perm ι}
-- given
  (hτ : ∀ i, ends (τ i) = ends i)
  (hτ2 : ∀ i, τ (τ i) = i)
  (hm : m.image τ = m) :
-- imply
  Function.Involutive (gc92b_pairAction (ι := ι) τ) ∧ (#(gc91b_cogxgPairs ends m o x g) = #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s)) + #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s ≠ s)) ∧ Even (#((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s ≠ s)))) ∧ (#((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s)) + #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s ≠ s)) / 2 ≤ #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s = s)) + #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s ≠ s)) / 2 ↔ #(gc91b_cogxgPairs ends m o x g) + #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s)) ≤ #(gc91b_T3Pairs ends m o x y g) + #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s = s))) := by
-- proof
  apply StatMech.Walls.gc93b_burnside_status ends m τ hτ hτ2 hm

/--
[gc93b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc93borbitcount.lean)
-/
@[path]
private lemma gc93b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc93b_machine_findings


-- created on 2026-10-23
