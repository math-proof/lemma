import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc91bglobalinjection
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc91b_ncount_eq_disjoint_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_ncount_eq_disjoint_count_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ : Finset ι}
-- given
  (hK₁m : K₁ ⊆ m) :
-- imply
  gc86b_ncount ends (m \ K₁) ∅ = #(m.powerset.filter (fun K₂ => Disjoint K₁ K₂ ∧ sources ends K₂ = (∅ : Finset W))) := by
-- proof
  apply StatMech.Walls.gc91b_ncount_eq_disjoint_count ends hK₁m

/--
[gc91b_cogxg_eq_card_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_cogxg_eq_card_pairs_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hxg : x ≠ g) :
-- imply
  gc85b_pcount ends m {o, g} {x, g} = #(gc91b_cogxgPairs ends m o x g) := by
-- proof
  apply StatMech.Walls.gc91b_cogxg_eq_card_pairs ends m hnd hxg

/--
[gc91b_T3_eq_card_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_T3_eq_card_pairs_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc87b_T3 ends m o x y g = #(gc91b_T3Pairs ends m o x y g) := by
-- proof
  apply StatMech.Walls.gc91b_T3_eq_card_pairs ends m o x y g

/--
[gc91b_cogxg_le_T3_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_cogxg_le_T3_of_injection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {f : Finset ι × Finset ι → Finset ι × Finset ι}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hxg : x ≠ g)
  (hmaps : ∀ KK ∈ gc91b_cogxgPairs ends m o x g, f KK ∈ gc91b_T3Pairs ends m o x y g)
  (hinj : Set.InjOn f (gc91b_cogxgPairs ends m o x g)) :
-- imply
  gc87b_CogxgLeT3 ends m o x y g := by
-- proof
  apply StatMech.Walls.gc91b_cogxg_le_T3_of_injection ends m hnd hxg f hmaps hinj

/--
[gc91b_close_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_close_of_injection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {f : Finset ι × Finset ι → Finset ι × Finset ι}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (hmaps : ∀ KK ∈ gc91b_cogxgPairs ends m o x g, f KK ∈ gc91b_T3Pairs ends m o x y g)
  (hinj : Set.InjOn f (gc91b_cogxgPairs ends m o x g)) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc91b_close_of_injection ends m hnd hsrc hox hoy hog hxg f hmaps hinj

/--
[gc91b_boundary_reroute_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_boundary_reroute_total_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {KK JJ : Finset ι × Finset ι}
-- given
  (hKK : KK ∈ gc91b_cogxgPairs ends m o x g)
  (hJJ : JJ ∈ gc91b_T3Pairs ends m o x y g) :
-- imply
  sources ends (KK.1 ∆ JJ.1) = ({o, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc91b_boundary_reroute_total ends m hKK hJJ

/--
[gc91b_boundary_marriage_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_boundary_marriage_iff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hxg : x ≠ g) :
-- imply
  Nonempty ({KK // KK ∈ gc91b_cogxgPairs ends m o x g} ↪ {JJ // JJ ∈ gc91b_T3Pairs ends m o x y g}) ↔ gc87b_CogxgLeT3 ends m o x y g := by
-- proof
  apply StatMech.Walls.gc91b_boundary_marriage_iff ends m hnd hxg

/--
[gc91b_star_boundary_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_star_boundary_total_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  sources gc90b_starEnds ({2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) ∧ sources gc90b_starEnds ({2, 3} : Finset (Fin 5)) = (∅ : Finset (Fin 4)) ∧ ¬ (({2, 3} : Finset (Fin 5)) ⊆ ({2} : Finset (Fin 5))) ∧ sources gc90b_starEnds (({2} : Finset (Fin 5)) ∆ ({2, 3} : Finset (Fin 5))) = ({0, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc91b_star_boundary_total

/--
[gc91b_global_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_global_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxg : x ≠ g) :
-- imply
  (gc85b_pcount ends m {o, g} {x, g} = #(gc91b_cogxgPairs ends m o x g) ∧ gc87b_T3 ends m o x y g = #(gc91b_T3Pairs ends m o x y g)) ∧ (∀ f : Finset ι × Finset ι → Finset ι × Finset ι, (∀ KK ∈ gc91b_cogxgPairs ends m o x g, f KK ∈ gc91b_T3Pairs ends m o x y g) → Set.InjOn f (gc91b_cogxgPairs ends m o x g) → gc85b_ThreeCurrentBijection ends m o x y g) ∧ (∀ {KK JJ : Finset ι × Finset ι}, KK ∈ gc91b_cogxgPairs ends m o x g → JJ ∈ gc91b_T3Pairs ends m o x y g → sources ends (KK.1 ∆ JJ.1) = ({o, g} : Finset W)) := by
-- proof
  apply StatMech.Walls.gc91b_global_status ends m hnd hsrc hox hoy hog hxg

/--
[gc91b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean)
-/
@[path]
private lemma gc91b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc91b_machine_findings


-- created on 2026-10-23
