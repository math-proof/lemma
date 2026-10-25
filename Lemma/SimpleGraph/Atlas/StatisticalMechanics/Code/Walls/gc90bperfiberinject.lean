import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc90bperfiberinject.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc90b_ncount_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_ncount_mono_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R R' : Finset ι}
-- given
  (hRR : R ⊆ R') :
-- imply
  gc86b_ncount ends R ∅ ≤ gc86b_ncount ends R' ∅ := by
-- proof
  apply StatMech.Walls.gc90b_ncount_mono ends hRR

/--
[gc90b_perK1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_perK1_le_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ P : Finset ι}
-- given
  (hP : P ⊆ K₁) :
-- imply
  gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ (K₁ \ P)) ∅ := by
-- proof
  apply StatMech.Walls.gc90b_perK1_le ends hP

/--
[gc90b_cogxg_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_cogxg_eq_sum_eq
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
  gc85b_pcount ends m {o, g} {x, g} = ∑ K₁ ∈ gc90b_cogxgFibers ends m o x g, gc86b_ncount ends (m \ K₁) ∅ := by
-- proof
  apply StatMech.Walls.gc90b_cogxg_eq_sum ends m hnd hxg

/--
[gc90b_T3_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_T3_eq_sum_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc87b_T3 ends m o x y g = ∑ J₁ ∈ gc90b_T3Fibers ends m o x y g, gc86b_ncount ends (m \ J₁) ∅ := by
-- proof
  apply StatMech.Walls.gc90b_T3_eq_sum ends m o x y g

/--
[gc90b_cogxg_le_of_assignment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_cogxg_le_of_assignment_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {φ : Finset ι → Finset ι}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hxg : x ≠ g)
  (hφmem : ∀ K₁ ∈ gc90b_cogxgFibers ends m o x g, φ K₁ ∈ gc90b_T3Fibers ends m o x y g)
  (hcap : ∀ J₁ ∈ gc90b_T3Fibers ends m o x y g, ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁), gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ J₁) ∅) :
-- imply
  gc85b_pcount ends m {o, g} {x, g} ≤ gc87b_T3 ends m o x y g := by
-- proof
  apply StatMech.Walls.gc90b_cogxg_le_of_assignment ends m hnd hxg φ hφmem hcap

/--
[gc90b_close_of_assignment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_close_of_assignment_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {φ : Finset ι → Finset ι}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (hφmem : ∀ K₁ ∈ gc90b_cogxgFibers ends m o x g, φ K₁ ∈ gc90b_T3Fibers ends m o x y g)
  (hcap : ∀ J₁ ∈ gc90b_T3Fibers ends m o x y g, ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁), gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ J₁) ∅) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc90b_close_of_assignment ends m hnd hsrc hox hoy hog hxg φ hφmem hcap

/--
[gc90b_star_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_star_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  sources gc90b_starEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc90b_star_sources

/--
[gc90b_star_cogxgFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_star_cogxgFibers_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  sources gc90b_starEnds ({2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) ∧ sources gc90b_starEnds ({3} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) ∧ sources gc90b_starEnds ({4} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc90b_star_cogxgFibers

/--
[gc90b_star_canonical_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_star_canonical_merge_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (({2} : Finset (Fin 5)) \ ({2} : Finset (Fin 5)) = (∅ : Finset (Fin 5))) ∧ (({3} : Finset (Fin 5)) \ ({3} : Finset (Fin 5)) = (∅ : Finset (Fin 5))) ∧ (({4} : Finset (Fin 5)) \ ({4} : Finset (Fin 5)) = (∅ : Finset (Fin 5))) := by
-- proof
  apply StatMech.Walls.gc90b_star_canonical_merge

/--
[gc90b_star_perJ1_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_star_perJ1_fails_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ ({2} : Finset (Fin 5))) ∅ = 2 ∧ gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ ({3} : Finset (Fin 5))) ∅ = 2 ∧ gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ ({4} : Finset (Fin 5))) ∅ = 2 ∧ gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ (∅ : Finset (Fin 5))) ∅ = 4 ∧ (2 + 2 + 2 : ℕ) > gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ (∅ : Finset (Fin 5))) ∅ := by
-- proof
  apply StatMech.Walls.gc90b_star_perJ1_fails

/--
[gc90b_perfiber_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_perfiber_status_eq
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
  (∀ (K₁ P : Finset ι), P ⊆ K₁ → gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ (K₁ \ P)) ∅) ∧ (∀ (φ : Finset ι → Finset ι), (∀ K₁ ∈ gc90b_cogxgFibers ends m o x g, φ K₁ ∈ gc90b_T3Fibers ends m o x y g) → (∀ J₁ ∈ gc90b_T3Fibers ends m o x y g, ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁), gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ J₁) ∅) → gc85b_ThreeCurrentBijection ends m o x y g) := by
-- proof
  apply StatMech.Walls.gc90b_perfiber_status ends m hnd hsrc hox hoy hog hxg

/--
[gc90b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean)
-/
@[path]
private lemma gc90b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc90b_machine_findings


-- created on 2026-10-23
