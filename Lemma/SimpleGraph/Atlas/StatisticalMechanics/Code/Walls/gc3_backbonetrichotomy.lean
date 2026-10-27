import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc3_backbonetrichotomy
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc3_third_of_two_ox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_third_of_two_ox_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hxy : connK ends m x y)
  (hoy : connK ends m o y) :
-- imply
  connK ends m o x := by
-- proof
  apply StatMech.Walls.gc3_third_of_two_ox ends m hxy hoy

/--
[gc3_third_of_two_oy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_third_of_two_oy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hxy : connK ends m x y)
  (hox : connK ends m o x) :
-- imply
  connK ends m o y := by
-- proof
  apply StatMech.Walls.gc3_third_of_two_oy ends m hxy hox

/--
[gc3_third_of_two_xy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_third_of_two_xy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hoy : connK ends m o y)
  (hox : connK ends m o x) :
-- imply
  connK ends m x y := by
-- proof
  apply StatMech.Walls.gc3_third_of_two_xy ends m hoy hox

/--
[gc3_no_exactlyTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_no_exactlyTwo_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  ¬ ((connK ends m x y ∧ connK ends m o y ∧ ¬ connK ends m o x) ∨ (connK ends m x y ∧ ¬ connK ends m o y ∧ connK ends m o x) ∨ (¬ connK ends m x y ∧ connK ends m o y ∧ connK ends m o x)) := by
-- proof
  apply StatMech.Walls.gc3_no_exactlyTwo ends m

/--
[gc3_connCount_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_connCount_trichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  (¬ connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x) ∨ ((connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x) ∨ (¬ connK ends m x y ∧ connK ends m o y ∧ ¬ connK ends m o x) ∨ (¬ connK ends m x y ∧ ¬ connK ends m o y ∧ connK ends m o x)) ∨ (connK ends m x y ∧ connK ends m o y ∧ connK ends m o x) := by
-- proof
  apply StatMech.Walls.gc3_connCount_trichotomy ends m o x y

/--
[gc3_backboneFactor_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_backboneFactor_trichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  asd_ghsBackboneFactor ends m o x y = 1 ∨ asd_ghsBackboneFactor ends m o x y = 0 ∨ asd_ghsBackboneFactor ends m o x y = -2 := by
-- proof
  apply StatMech.Walls.gc3_backboneFactor_trichotomy ends m o x y

/--
[gc3_backboneFactor_ne_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_backboneFactor_ne_neg_one_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  asd_ghsBackboneFactor ends m o x y ≠ -1 := by
-- proof
  apply StatMech.Walls.gc3_backboneFactor_ne_neg_one ends m o x y

/--
[gc3_backboneFactor_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_backboneFactor_eq_one_iff_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  asd_ghsBackboneFactor ends m o x y = 1 ↔ (¬ connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x) := by
-- proof
  apply StatMech.Walls.gc3_backboneFactor_eq_one_iff ends m o x y

/--
[gc3_backboneFactor_eq_neg_two_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_backboneFactor_eq_neg_two_iff_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  asd_ghsBackboneFactor ends m o x y = -2 ↔ (connK ends m x y ∧ connK ends m o y ∧ connK ends m o x) := by
-- proof
  apply StatMech.Walls.gc3_backboneFactor_eq_neg_two_iff ends m o x y

/--
[gc3_backboneFactor_eq_zero_of_exactlyOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_backboneFactor_eq_zero_of_exactlyOne_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (h : (connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x) ∨ (¬ connK ends m x y ∧ connK ends m o y ∧ ¬ connK ends m o x) ∨ (¬ connK ends m x y ∧ ¬ connK ends m o y ∧ connK ends m o x)) :
-- imply
  asd_ghsBackboneFactor ends m o x y = 0 := by
-- proof
  apply StatMech.Walls.gc3_backboneFactor_eq_zero_of_exactlyOne ends m h

/--
[gc3_signed_eq_mass_mul_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_signed_eq_mass_mul_factor_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K) = (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) * asd_ghsBackboneFactor ends m o x y := by
-- proof
  apply StatMech.Walls.gc3_signed_eq_mass_mul_factor ends m hnd A hm hox hoy hxy φ hφ

/--
[gc3_signed_eq_mass_mul_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_signed_eq_mass_mul_trichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  ∃ c : ℝ, (c = 1 ∨ c = 0 ∨ c = -2) ∧ (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K) = (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) * c := by
-- proof
  apply StatMech.Walls.gc3_signed_eq_mass_mul_trichotomy ends m hnd A hm hox hoy hxy φ hφ

/--
[gc3_backboneFactor_trichotomy_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_backboneFactor_trichotomy_current_eq
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
  {o x y : W} :
-- imply
  asd_ghsBackboneFactor (endsM G m) M o x y = 1 ∨ asd_ghsBackboneFactor (endsM G m) M o x y = 0 ∨ asd_ghsBackboneFactor (endsM G m) M o x y = -2 := by
-- proof
  apply StatMech.Walls.gc3_backboneFactor_trichotomy_current G m M o x y

/--
[gc3_no_exactlyTwo_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonetrichotomy.lean)
-/
@[path]
private lemma gc3_no_exactlyTwo_current_eq
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
  {o x y : W} :
-- imply
  ¬ ((connK (endsM G m) M x y ∧ connK (endsM G m) M o y ∧ ¬ connK (endsM G m) M o x) ∨ (connK (endsM G m) M x y ∧ ¬ connK (endsM G m) M o y ∧ connK (endsM G m) M o x) ∨ (¬ connK (endsM G m) M x y ∧ connK (endsM G m) M o y ∧ connK (endsM G m) M o x)) := by
-- proof
  apply StatMech.Walls.gc3_no_exactlyTwo_current G m M


-- created on 2026-10-23
