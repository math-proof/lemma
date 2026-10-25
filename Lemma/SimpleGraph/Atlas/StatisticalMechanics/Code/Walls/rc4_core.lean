import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc4_core
open Finset StatMech StatMech.Walls


/--
[rc4_filter_card_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_filter_card_congr_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [Fintype F]
  {g : E ≃ F}
  [DecidablePred P]
  [DecidablePred (fun y => P (g.symm y))]
-- given
  (P : E → Prop) :
-- imply
  #(univ.filter P) = #(univ.filter (fun y => P (g.symm y))) := by
-- proof
  apply StatMech.Walls.rc4_filter_card_congr g P

/--
[rc4_compl_cfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_compl_cfgEquiv_eq
  [Fintype α]
  [DecidableEq α]
  {e : E ≃ F}
  {ωf : ConfigSpace F} :
-- imply
  (fun a => !(cfgEquiv e ωf a)) = cfgEquiv e (fun y => !ωf y) := by
-- proof
  apply StatMech.Walls.rc4_compl_cfgEquiv e ωf

/--
[rc4_reimerCardForm_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_reimerCardForm_transfer_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)}
-- given
  (hcard : ReimerCardFormAll) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc4_reimerCardForm_transfer hcard A B

/--
[rc4_unrestrict_restrict_of_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_unrestrict_restrict_of_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
-- given
  (hω : ω ∈ rc2_slab k) :
-- imply
  pocUnrestrict k (pocRestrict k ω) = ω := by
-- proof
  apply StatMech.Walls.rc4_unrestrict_restrict_of_slab hω

/--
[rc4_keyFlip_eq_unrestrict_compl_of_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_keyFlip_eq_unrestrict_compl_of_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
-- given
  (hω : ω ∈ rc2_slab k) :
-- imply
  poc_keyFlip k ω = pocUnrestrict k (rmr_compl (pocRestrict k ω)) := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_eq_unrestrict_compl_of_slab hω

/--
[rc4_unrestrict_mem_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_unrestrict_mem_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {σ : ConfigSpace (DifferSub k)}
-- given
  (hvalid : ∀ a, k.1 a ≠ k.2 a → (k.1 a = true ∧ k.2 a = false)) :
-- imply
  pocUnrestrict k σ ∈ rc2_slab k := by
-- proof
  apply StatMech.Walls.rc4_unrestrict_mem_slab hvalid σ

/--
[rc4_rhs_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_rhs_card_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {A B : Set (ConfigSpace α)}
-- given
  (hvalid : ∀ a, k.1 a ≠ k.2 a → (k.1 a = true ∧ k.2 a = false)) :
-- imply
  #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k)) = #(univ.filter (fun σ : ConfigSpace (DifferSub k) => σ ∈ pocFrozenRestrict k A ∧ (fun a => !σ a) ∈ pocFrozenRestrict k B)) := by
-- proof
  apply StatMech.Walls.rc4_rhs_card k hvalid A B

/--
[rc4_pocRestrictWitness_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_pocRestrictWitness_disjoint_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {K L : Set α}
-- given
  (h : Disjoint K L) :
-- imply
  Disjoint (pocRestrictWitness k K) (pocRestrictWitness k L) := by
-- proof
  apply StatMech.Walls.rc4_pocRestrictWitness_disjoint h

/--
[rc4_box_restrict_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_box_restrict_mem_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α}
-- given
  (hslab : ω ∈ rc2_slab k)
  (hbox : ω ∈ disjointOccurrence A B) :
-- imply
  pocRestrict k ω ∈ disjointOccurrence (pocFrozenRestrict k A) (pocFrozenRestrict k B) := by
-- proof
  apply StatMech.Walls.rc4_box_restrict_mem hslab hbox

/--
[rc4_lhs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_lhs_le_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {A B : Set (ConfigSpace α)} :
-- imply
  #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)) ≤ #(univ.filter (fun σ : ConfigSpace (DifferSub k) => σ ∈ disjointOccurrence (pocFrozenRestrict k A) (pocFrozenRestrict k B))) := by
-- proof
  apply StatMech.Walls.rc4_lhs_le k A B

/--
[rc4_perKey_of_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_perKey_of_reimerCardFormAll_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hcard : ReimerCardFormAll)
  (hvalid : ∀ a, k.1 a ≠ k.2 a → (k.1 a = true ∧ k.2 a = false)) :
-- imply
  rc3_PerKey A B k := by
-- proof
  apply StatMech.Walls.rc4_perKey_of_reimerCardFormAll hcard A B hvalid

/--
[rc4_perKey_all_of_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_perKey_all_of_reimerCardFormAll_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hcard : ReimerCardFormAll) :
-- imply
  rc3_PerKey A B k := by
-- proof
  apply StatMech.Walls.rc4_perKey_all_of_reimerCardFormAll hcard A B k

/--
[rc4_reimerSubcubeReduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_reimerSubcubeReduction_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ReimerSubcubeReduction := by
-- proof
  apply StatMech.Walls.rc4_reimerSubcubeReduction

/--
[rc4_residue_of_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_residue_of_reimerCardFormAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (hcard : ReimerCardFormAll) :
-- imply
  ReimerResidue := by
-- proof
  apply StatMech.Walls.rc4_residue_of_reimerCardFormAll hcard

/--
[rc4_perKeyAll_of_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_perKeyAll_of_reimerCardFormAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (hcard : ReimerCardFormAll) :
-- imply
  rc3_PerKeyAll := by
-- proof
  apply StatMech.Walls.rc4_perKeyAll_of_reimerCardFormAll hcard

/--
[rc4_reimer_inequality_of_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_reimer_inequality_of_reimerCardFormAll_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (hcard : ReimerCardFormAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc4_reimer_inequality_of_reimerCardFormAll hcard hp A B

/--
[rc4_residue_iff_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_core.lean)
-/
@[path]
private lemma rc4_residue_iff_reimerCardFormAll_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ReimerResidue ↔ ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc4_residue_iff_reimerCardFormAll


-- created on 2026-10-23
