import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc42countproof
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc42_pairCount_reindex_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_pairCount_reindex_union_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [DecidablePred P]
  [∀ a, DecidablePred (Q a)]
-- given
  (P : Finset ι → Prop)
  (Q : Finset ι → Finset ι → Prop) :
-- imply
  #((univ : Finset (Finset ι × Finset ι)).filter (fun p => p.2 ⊆ univ \ p.1 ∧ P (p.1 ∪ p.2) ∧ Q (p.1 ∪ p.2) p.1)) = ∑ M ∈ (univ : Finset ι).powerset.filter (fun S => P S), #(M.powerset.filter (fun S₁ => Q M S₁)) := by
-- proof
  apply StatMech.Walls.gc42_pairCount_reindex_union P Q

/--
[gc42_sd_og_xg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_sd_og_xg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {o x g : W}
-- given
  (hox : o ≠ x)
  (hog : o ≠ g)
  (hxg : x ≠ g) :
-- imply
  ({o, g} : Finset W) ∆ ({x, g} : Finset W) = ({o, x} : Finset W) := by
-- proof
  apply StatMech.Walls.gc42_sd_og_xg hox hog hxg

/--
[gc42_union_sources_ox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_union_sources_ox_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {S₁ S₂ : Finset ι}
  {o x g : W}
-- given
  (hd : S₂ ⊆ univ \ S₁)
  (hox : o ≠ x)
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (h0 : sources ends S₁ = ({o, g} : Finset W))
  (h1 : sources ends S₂ = ({x, g} : Finset W)) :
-- imply
  sources ends (S₁ ∪ S₂) = ({o, x} : Finset W) := by
-- proof
  apply StatMech.Walls.gc42_union_sources_ox ends hd hox hog hxg h0 h1

/--
[gc42_sd_ox_xg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_sd_ox_xg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {o x g : W}
-- given
  (hox : o ≠ x)
  (hog : o ≠ g)
  (hxg : x ≠ g) :
-- imply
  ({o, x} : Finset W) ∆ ({x, g} : Finset W) = ({o, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc42_sd_ox_xg hox hog hxg

/--
[gc42_inner_count_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_inner_count_collapse_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
  {o x g : W}
-- given
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag)
  (hMsrc : sources ends M = ({o, x} : Finset W))
  (hox : o ≠ x)
  (hog : o ≠ g)
  (hxg : x ≠ g) :
-- imply
  #(M.powerset.filter (fun S₁ => sources ends S₁ = ({o, g} : Finset W))) = (if connK ends M x g then gc40_E ends M else 0) := by
-- proof
  apply StatMech.Walls.gc42_inner_count_collapse ends M hnd hMsrc hox hog hxg

/--
[gc42_NR_eq_Mform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_NR_eq_Mform_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
-- imply
  gc40_NR ends o x y g = ∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)), (if connK ends M x g then gc40_E ends M else 0) := by
-- proof
  apply StatMech.Walls.gc42_NR_eq_Mform ends hnd hox hoy hog hxy hxg hyg huniv

/--
[gc42_full_boundary_count_eq_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_full_boundary_count_eq_E_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι} :
-- imply
  #(M.powerset.filter (fun S => sources ends S = sources ends M)) = gc40_E ends M := by
-- proof
  apply StatMech.Walls.gc42_full_boundary_count_eq_E ends M

/--
[gc42_NL_eq_Mform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_NL_eq_Mform_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
-- imply
  gc40_NL ends o x y g = ∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)), (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0) := by
-- proof
  apply StatMech.Walls.gc42_NL_eq_Mform ends huniv

/--
[gc42_countIneq_of_EMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_countIneq_of_EMass_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hres : gc42_EMassResidue ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc42_countIneq_of_EMass ends hnd hox hoy hog hxy hxg hyg huniv hres

/--
[gc42_NRterm_le_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_NRterm_le_E_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
  {x g : W} :
-- imply
  (if connK ends M x g then gc40_E ends M else 0) ≤ gc40_E ends M := by
-- proof
  apply StatMech.Walls.gc42_NRterm_le_E ends M

/--
[gc42_NLterm_le_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_NLterm_le_E_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
  {o x y g : W} :
-- imply
  (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0) ≤ gc40_E ends M := by
-- proof
  apply StatMech.Walls.gc42_NLterm_le_E ends M

/--
[gc42_EMass_iff_countIneq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_EMass_iff_countIneq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
-- imply
  gc42_EMassResidue ends o x y g ↔ gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc42_EMass_iff_countIneq ends hnd hox hoy hog hxy hxg hyg huniv

/--
[gc42_reduction_applies_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_reduction_applies_claw_eq :
-- imply
  (∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag) ∧ ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3 ∧ (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3) ∧ sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc42_reduction_applies_claw

/--
[gc42_claw_residue_closes_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_claw_residue_closes_core_eq
-- given
  (hres : gc42_EMassResidue gc40_clawEnds (0 : Fin 4) 1 2 3) :
-- imply
  gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc42_claw_residue_closes_core hres

/--
[gc42_claw_EMassResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_claw_EMassResidue_eq :
-- imply
  gc42_EMassResidue gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc42_claw_EMassResidue

/--
[gc42_claw_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean)
-/
@[path]
private lemma gc42_claw_core_eq :
-- imply
  gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc42_claw_core


-- created on 2026-10-23
