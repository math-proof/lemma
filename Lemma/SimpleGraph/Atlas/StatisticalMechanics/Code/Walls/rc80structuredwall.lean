import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall.Part3
open Finset StatMech StatMech.Walls


/--
[rc80_minext_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_minext_agree_eq
  [Fintype ι]
  [DecidableEq ι]
  {K : Finset ι}
  {w : ConfigSpace ι}
  {e : ι}
-- given
  (he : e ∈ K) :
-- imply
  rc80_minext K w e = w e := by
-- proof
  apply StatMech.Walls.rc80_minext_agree K w he

/--
[rc80_maxext_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_maxext_agree_eq
  [Fintype ι]
  [DecidableEq ι]
  {L : Finset ι}
  {w : ConfigSpace ι}
  {e : ι}
-- given
  (he : e ∈ L) :
-- imply
  rc80_maxext L w e = w e := by
-- proof
  apply StatMech.Walls.rc80_maxext_agree L w he

/--
[rc80_minext_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_minext_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {K : Finset ι}
  {w : ConfigSpace ι}
  {i : ι} :
-- imply
  rc80_minext K w i = true → w i = true := by
-- proof
  apply StatMech.Walls.rc80_minext_le K w i

/--
[rc80_le_maxext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_le_maxext_eq
  [Fintype ι]
  [DecidableEq ι]
  {L : Finset ι}
  {w : ConfigSpace ι}
  {i : ι} :
-- imply
  w i = true → rc80_maxext L w i = true := by
-- proof
  apply StatMech.Walls.rc80_le_maxext L w i

/--
[rc80_upper_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_upper_mono_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
  {a b : ConfigSpace ι}
-- given
  (hA : rc80_IsUpper A)
  (hab : ∀ i, a i = true → b i = true)
  (ha : a ∈ A) :
-- imply
  b ∈ A := by
-- proof
  apply StatMech.Walls.rc80_upper_mono hA hab ha

/--
[rc80_lower_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_lower_mono_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
  {a b : ConfigSpace ι}
-- given
  (hA : rc80_IsLower A)
  (hab : ∀ i, b i = true → a i = true)
  (ha : a ∈ A) :
-- imply
  b ∈ A := by
-- proof
  apply StatMech.Walls.rc80_lower_mono hA hab ha

/--
[rc80_occ_upper_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_occ_upper_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
  {K : Finset ι}
  {w : ConfigSpace ι}
-- given
  (hA : rc80_IsUpper A) :
-- imply
  rc80_occ A K w = true ↔ rc80_minext K w ∈ A := by
-- proof
  apply StatMech.Walls.rc80_occ_upper_iff hA K w

/--
[rc80_occ_lower_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_occ_lower_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)}
  {L : Finset ι}
  {w : ConfigSpace ι}
-- given
  (hB : rc80_IsLower B) :
-- imply
  rc80_occ B L w = true ↔ rc80_maxext L w ∈ B := by
-- proof
  apply StatMech.Walls.rc80_occ_lower_iff hB L w

/--
[rc80_disjOcc_eq_inter_of_upper_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_disjOcc_eq_inter_of_upper_lower_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (hA : rc80_IsUpper A)
  (hB : rc80_IsLower B) :
-- imply
  rc80_disjOccG A B = A ∩ B := by
-- proof
  apply StatMech.Walls.rc80_disjOcc_eq_inter_of_upper_lower hA hB

/--
[rc80_wall_upper_lower_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_wall_upper_lower_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (hA : rc80_IsUpper A)
  (hB : rc80_IsLower B) :
-- imply
  (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card ↔ (A ∩ B).card ≤ (rc80_reflInterG A B).card := by
-- proof
  apply StatMech.Walls.rc80_wall_upper_lower_iff hA hB

/--
[rc80_mem_prodFam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_mem_prodFam_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {A₁ : Finset (ConfigSpace ι)}
  {A₂ : Finset (ConfigSpace κ)}
  {w : ConfigSpace (ι ⊕ κ)} :
-- imply
  w ∈ rc80_prodFam A₁ A₂ ↔ rc80_restL w ∈ A₁ ∧ rc80_restR w ∈ A₂ := by
-- proof
  apply StatMech.Walls.rc80_mem_prodFam w

/--
[rc80_restL_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_restL_compl_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {w : ConfigSpace (ι ⊕ κ)} :
-- imply
  rc80_restL (rc80_compl w) = rc80_compl (rc80_restL w) := by
-- proof
  apply StatMech.Walls.rc80_restL_compl w

/--
[rc80_restR_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_restR_compl_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {w : ConfigSpace (ι ⊕ κ)} :
-- imply
  rc80_restR (rc80_compl w) = rc80_compl (rc80_restR w) := by
-- proof
  apply StatMech.Walls.rc80_restR_compl w

/--
[rc80_reflInter_prod_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_reflInter_prod_card_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {A₁ B₁ : Finset (ConfigSpace ι)}
  {A₂ B₂ : Finset (ConfigSpace κ)} :
-- imply
  (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card = (rc80_reflInterG A₁ B₁).card * (rc80_reflInterG A₂ B₂).card := by
-- proof
  apply StatMech.Walls.rc80_reflInter_prod_card A₁ B₁ A₂ B₂

/--
[rc80_mem_projL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_mem_projL_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {K : Finset (ι ⊕ κ)}
  {i : ι} :
-- imply
  i ∈ rc80_projL K ↔ Sum.inl i ∈ K := by
-- proof
  apply StatMech.Walls.rc80_mem_projL K i

/--
[rc80_mem_projR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_mem_projR_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {K : Finset (ι ⊕ κ)}
  {j : κ} :
-- imply
  j ∈ rc80_projR K ↔ Sum.inr j ∈ K := by
-- proof
  apply StatMech.Walls.rc80_mem_projR K j

/--
[rc80_occ_prodFam_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_occ_prodFam_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {A₁ : Finset (ConfigSpace ι)}
  {A₂ : Finset (ConfigSpace κ)}
  {K : Finset (ι ⊕ κ)}
  {w : ConfigSpace (ι ⊕ κ)} :
-- imply
  rc80_occ (rc80_prodFam A₁ A₂) K w = true ↔ rc80_occ A₁ (rc80_projL K) (rc80_restL w) = true ∧ rc80_occ A₂ (rc80_projR K) (rc80_restR w) = true := by
-- proof
  apply StatMech.Walls.rc80_occ_prodFam_iff A₁ A₂ K w

/--
[rc80_disjOcc_prod_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_disjOcc_prod_card_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {A₁ B₁ : Finset (ConfigSpace ι)}
  {A₂ B₂ : Finset (ConfigSpace κ)} :
-- imply
  (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card = (rc80_disjOccG A₁ B₁).card * (rc80_disjOccG A₂ B₂).card := by
-- proof
  apply StatMech.Walls.rc80_disjOcc_prod_card A₁ B₁ A₂ B₂

/--
[rc80_wall_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_wall_product_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
  {A₁ B₁ : Finset (ConfigSpace ι)}
  {A₂ B₂ : Finset (ConfigSpace κ)}
-- given
  (h0 : (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card)
  (h1 : (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card) :
-- imply
  (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card := by
-- proof
  apply StatMech.Walls.rc80_wall_product A₁ B₁ A₂ B₂ h0 h1

/--
[rc80_monoWitness_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_monoWitness_upper_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ] :
-- imply
  rc80_IsUpper ({(fun _ => true)} : Finset (ConfigSpace (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc80_monoWitness_upper

/--
[rc80_monoWitness_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_monoWitness_lower_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ] :
-- imply
  rc80_IsLower ({(fun _ => false)} : Finset (ConfigSpace (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc80_monoWitness_lower

/--
[rc80_monoWitness_reduces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_monoWitness_reduces_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ] :
-- imply
  rc80_disjOccG ({(fun _ => true)} : Finset (ConfigSpace (Fin 2))) {(fun _ => false)} = ({(fun _ => true)} : Finset (ConfigSpace (Fin 2))) ∩ {(fun _ => false)} := by
-- proof
  apply StatMech.Walls.rc80_monoWitness_reduces

/--
[rc80_prodWitness_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_prodWitness_reflInter_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ] :
-- imply
  (rc80_reflInterG (rc80_prodFam ({(fun _ => true)} : Finset (ConfigSpace (Fin 1))) ({(fun _ => true)} : Finset (ConfigSpace (Fin 1)))) (rc80_prodFam ({(fun _ => false)} : Finset (ConfigSpace (Fin 1))) ({(fun _ => false)} : Finset (ConfigSpace (Fin 1))))).card = (rc80_reflInterG ({(fun _ => true)} : Finset (ConfigSpace (Fin 1))) {(fun _ => false)}).card * (rc80_reflInterG ({(fun _ => true)} : Finset (ConfigSpace (Fin 1))) {(fun _ => false)}).card := by
-- proof
  apply StatMech.Walls.rc80_prodWitness_reflInter

/--
[rc80_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_reimerWprobCore_of_boxUnionBound_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ]
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc80_reimerWprobCore_of_boxUnionBound h

/--
[rc80_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean)
-/
@[path]
private lemma rc80_status_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype κ]
  [DecidableEq κ] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧ (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)), (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card = (rc80_disjOccG A₁ B₁).card * (rc80_disjOccG A₂ B₂).card) ∧ (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)), (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card = (rc80_reflInterG A₁ B₁).card * (rc80_reflInterG A₂ B₂).card) ∧ (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)), (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card → (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card → (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc80_status


-- created on 2026-10-23
