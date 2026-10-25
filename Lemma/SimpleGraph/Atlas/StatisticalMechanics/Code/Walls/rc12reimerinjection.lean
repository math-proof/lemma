import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part5
open Finset StatMech StatMech.Walls


/--
[rc12_mem_upGen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_mem_upGen_eq
  [Fintype α]
  [DecidableEq α]
  {L0 S : Finset α} :
-- imply
  S ∈ rc12_upGen L0 ↔ L0 ⊆ S := by
-- proof
  apply StatMech.Walls.rc12_mem_upGen L0 S

/--
[rc12_upGen_isUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_upGen_isUpper_eq
  [Fintype α]
  [DecidableEq α]
  {L0 : Finset α} :
-- imply
  IsUpperSet ((rc12_upGen L0 : Finset (Finset α)) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc12_upGen_isUpper L0

/--
[rc12_reflConstraint_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_reflConstraint_mem_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S T R : Finset α}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α)))
  (hT : T ∈ 𝒜)
  (hST : S \ T ∈ ℬ)
  (hTR : T ⊆ R)
  (hdisj : Disjoint R (S \ T)) :
-- imply
  R ∈ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc12_reflConstraint_mem_reflInter 𝒜 ℬ h𝒜 hℬ hT hST hTR hdisj

/--
[rc12_injection_of_reflectionInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_injection_of_reflectionInjection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α)))
  (h : rc12_ReimerReflectionInjection 𝒜 ℬ) :
-- imply
  rc11_BKRInjection 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc12_injection_of_reflectionInjection 𝒜 ℬ h𝒜 hℬ h

/--
[rc12_card_le_of_reflectionInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_card_le_of_reflectionInjection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α)))
  (h : rc12_ReimerReflectionInjection 𝒜 ℬ) :
-- imply
  #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc12_card_le_of_reflectionInjection 𝒜 ℬ h𝒜 hℬ h

/--
[rc12_boxSupp_principalRight_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_boxSupp_principalRight_iff_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {L0 S : Finset α} :
-- imply
  S ∈ rc10_boxSupp 𝒜 (rc12_upGen L0) ↔ L0 ⊆ S ∧ ∃ T ⊆ S, T ∈ 𝒜 ∧ Disjoint T L0 := by
-- proof
  apply StatMech.Walls.rc12_boxSupp_principalRight_iff 𝒜 L0 S

/--
[rc12_principalRight_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_principalRight_image_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {L0 : Finset α}
  {S : Finset α}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hS : S ∈ rc10_boxSupp 𝒜 (rc12_upGen L0)) :
-- imply
  (S \ L0) ∈ rc10_reflInter 𝒜 (rc12_upGen L0) := by
-- proof
  apply StatMech.Walls.rc12_principalRight_image 𝒜 h𝒜 L0 hS

/--
[rc12_principalRight_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_principalRight_injOn_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {L0 : Finset α} :
-- imply
  Set.InjOn (fun S => S \ L0) (rc10_boxSupp 𝒜 (rc12_upGen L0) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc12_principalRight_injOn 𝒜 L0

/--
[rc12_principalRight_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_principalRight_injection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {L0 : Finset α}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) :
-- imply
  rc11_BKRInjection 𝒜 (rc12_upGen L0) := by
-- proof
  apply StatMech.Walls.rc12_principalRight_injection 𝒜 h𝒜 L0

/--
[rc12_principalRight_reflectionInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_principalRight_reflectionInjection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {L0 : Finset α}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) :
-- imply
  rc12_ReimerReflectionInjection 𝒜 (rc12_upGen L0) := by
-- proof
  apply StatMech.Walls.rc12_principalRight_reflectionInjection 𝒜 h𝒜 L0

/--
[rc12_boxSupp_principalLeft_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_boxSupp_principalLeft_iff_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
  {T0 S : Finset α}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  S ∈ rc10_boxSupp (rc12_upGen T0) ℬ ↔ T0 ⊆ S ∧ S \ T0 ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc12_boxSupp_principalLeft_iff ℬ hℬ T0 S

/--
[rc12_principalLeft_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_principalLeft_image_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
  {T0 : Finset α}
  {S : Finset α}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α)))
  (hS : S ∈ rc10_boxSupp (rc12_upGen T0) ℬ) :
-- imply
  (Sᶜ ∪ T0) ∈ rc10_reflInter (rc12_upGen T0) ℬ := by
-- proof
  apply StatMech.Walls.rc12_principalLeft_image ℬ hℬ T0 hS

/--
[rc12_principalLeft_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_principalLeft_injOn_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
  {T0 : Finset α}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  Set.InjOn (fun S => Sᶜ ∪ T0) (rc10_boxSupp (rc12_upGen T0) ℬ : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc12_principalLeft_injOn ℬ hℬ T0

/--
[rc12_principalLeft_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_principalLeft_injection_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
  {T0 : Finset α}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  rc11_BKRInjection (rc12_upGen T0) ℬ := by
-- proof
  apply StatMech.Walls.rc12_principalLeft_injection ℬ hℬ T0

/--
[rc12_principalLeft_reflectionInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_principalLeft_reflectionInjection_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
  {T0 : Finset α}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  rc12_ReimerReflectionInjection (rc12_upGen T0) ℬ := by
-- proof
  apply StatMech.Walls.rc12_principalLeft_reflectionInjection ℬ hℬ T0

/--
[rc12_residue_realised_principalRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_residue_realised_principalRight_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 : Finset (Finset (Fin n))}
  {L0 : Finset (Fin n)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n)))) :
-- imply
  rc12_ReimerReflectionInjection 𝒜 (rc12_upGen L0) ∧ rc11_BKRInjection 𝒜 (rc12_upGen L0) ∧ #(rc10_boxSupp 𝒜 (rc12_upGen L0)) ≤ #(rc10_reflInter 𝒜 (rc12_upGen L0)) := by
-- proof
  apply StatMech.Walls.rc12_residue_realised_principalRight n 𝒜 h𝒜 L0

/--
[rc12_residue_realised_principalLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_residue_realised_principalLeft_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {ℬ : Finset (Finset (Fin n))}
  {T0 : Finset (Fin n)}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
-- imply
  rc12_ReimerReflectionInjection (rc12_upGen T0) ℬ ∧ rc11_BKRInjection (rc12_upGen T0) ℬ ∧ #(rc10_boxSupp (rc12_upGen T0) ℬ) ≤ #(rc10_reflInter (rc12_upGen T0) ℬ) := by
-- proof
  apply StatMech.Walls.rc12_residue_realised_principalLeft n ℬ hℬ T0

/--
[rc12_boxSuppComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_boxSuppComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc12_boxSuppComp 𝒜 ℬ = rc10_boxSupp 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc12_boxSuppComp_eq 𝒜 ℬ

/--
[rc12_reflInterComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_reflInterComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc12_reflInterComp 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc12_reflInterComp_eq 𝒜 ℬ

/--
[rc12_isUpperFin_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_isUpperFin_iff_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 : Finset (Finset (Fin n))} :
-- imply
  rc12_isUpperFin n 𝒜 ↔ IsUpperSet (𝒜 : Set (Finset (Fin n))) := by
-- proof
  apply StatMech.Walls.rc12_isUpperFin_iff n 𝒜

/--
[rc12_reflInjSearch_fin2_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_reflInjSearch_fin2_holds_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ → rc12_reflInjSearch 𝒜 ℬ = true := by
-- proof
  apply StatMech.Walls.rc12_reflInjSearch_fin2_holds

/--
[rc12_naiveUnion_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean)
-/
@[path]
private lemma rc12_naiveUnion_refuted_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc12_naiveUnionSearch ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) Finset.univ = false := by
-- proof
  apply StatMech.Walls.rc12_naiveUnion_refuted


-- created on 2026-10-23
