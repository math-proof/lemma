import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc23boxmono
open Finset StatMech StatMech.Walls


/--
[rc23_compl_inter_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_compl_inter_eq_iff_eq
  [Fintype α]
  [DecidableEq α]
  {U S K : Finset α} :
-- imply
  Uᶜ ∩ K = Sᶜ ∩ K ↔ U ∩ K = S ∩ K := by
-- proof
  apply StatMech.Walls.rc23_compl_inter_eq_iff U S K

/--
[rc23_traceCond_complFam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_traceCond_complFam_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {K S : Finset α} :
-- imply
  (∀ T : Finset α, T ∩ K = Sᶜ ∩ K → T ∈ rc22_complFam 𝒜) ↔ (∀ U : Finset α, U ∩ K = S ∩ K → U ∈ 𝒜) := by
-- proof
  apply StatMech.Walls.rc23_traceCond_complFam 𝒜 K S

/--
[rc23_mem_famCylBox_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_mem_famCylBox_compl_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc20_famCylBox 𝒜 ℬ ↔ Sᶜ ∈ rc20_famCylBox (rc22_complFam 𝒜) (rc22_complFam ℬ) := by
-- proof
  apply StatMech.Walls.rc23_mem_famCylBox_compl 𝒜 ℬ S

/--
[rc23_famCylBox_image_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_famCylBox_image_compl_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (rc20_famCylBox 𝒜 ℬ).image compl = rc20_famCylBox (rc22_complFam 𝒜) (rc22_complFam ℬ) := by
-- proof
  apply StatMech.Walls.rc23_famCylBox_image_compl 𝒜 ℬ

/--
[rc23_card_famCylBox_complFam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_card_famCylBox_complFam_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) = #(rc20_famCylBox (rc22_complFam 𝒜) (rc22_complFam ℬ)) := by
-- proof
  apply StatMech.Walls.rc23_card_famCylBox_complFam 𝒜 ℬ

/--
[rc23_complFam_isUpperSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_complFam_isUpperSet_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  IsUpperSet (rc22_complFam 𝒜 : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc23_complFam_isUpperSet h𝒜

/--
[rc23_card_reflInter_complFam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_card_reflInter_complFam_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter (rc22_complFam 𝒜) (rc22_complFam ℬ)) = #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc23_card_reflInter_complFam 𝒜 ℬ

/--
[rc23_boxDownsetBase_proof](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_boxDownsetBase_proof_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset (Fin n))))
  (hℬ : IsLowerSet (ℬ : Set (Finset (Fin n)))) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc23_boxDownsetBase_proof h𝒜 hℬ

/--
[rc23_boxDownsetBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_boxDownsetBase_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc22_BoxDownsetBase := by
-- proof
  apply StatMech.Walls.rc23_boxDownsetBase

/--
[rc23_famCylBox_downDown_strictDecrease](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_famCylBox_downDown_strictDecrease_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox (Down.compression 0 ({{0}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3)))) (Down.compression 0 ({∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))))) < #(rc20_famCylBox ({{0}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))) ({∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,1,2}})) := by
-- proof
  apply StatMech.Walls.rc23_famCylBox_downDown_strictDecrease

/--
[rc23_boxCompressionMono_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_boxCompressionMono_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rc22_BoxCompressionMono := by
-- proof
  apply StatMech.Walls.rc23_boxCompressionMono_false

/--
[rc23_wall_still_holds_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_wall_still_holds_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc23_wall_still_holds_fin2 𝒜 ℬ

/--
[rc23_boxDownsetBase_strict_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_boxDownsetBase_strict_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3))) ({∅, {0}, {1}, {2}, {0,2}, {1,2}})) < #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 3))) ({∅, {0}, {1}, {2}, {0,2}, {1,2}})) := by
-- proof
  apply StatMech.Walls.rc23_boxDownsetBase_strict_witness

/--
[rc23_reimer_boxmono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc23boxmono.lean)
-/
@[path]
private lemma rc23_reimer_boxmono_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc22_BoxDownsetBase ∧ (¬ rc22_BoxCompressionMono) ∧ (#(rc20_famCylBox (Down.compression 0 ({{0}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3)))) (Down.compression 0 ({∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))))) < #(rc20_famCylBox ({{0}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))) ({∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,1,2}}))) ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc23_reimer_boxmono


-- created on 2026-10-23
