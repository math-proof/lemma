/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Profinite
import Def.StatisticalMechanics.Code.Probability.MeasurableFKGClosure
open Filter MeasureTheory Set Topology


namespace StatMech

variable {E : Type*} [DecidableEq E] [Countable E]

theorem finiteUpwardHull_dependsOn
    (F : Finset E) (A : Set (ConfigSpace E)) :
    DependsOn (finiteUpwardHull F A) (F : Set E) := by
  intro eta theta hagree
  constructor
  · rintro ⟨omega, homega, hle⟩
    exact ⟨omega, homega, fun e he => by
      rw [hagree e he]
      exact hle e he⟩
  · rintro ⟨omega, homega, hle⟩
    exact ⟨omega, homega, fun e he => by
      rw [← hagree e he]
      exact hle e he⟩

theorem finiteUpwardHull_isClopen
    (F : Finset E) (A : Set (ConfigSpace E)) :
    IsClopen (finiteUpwardHull F A) :=
  isClopen_of_dependsOn_finset _ F (finiteUpwardHull_dependsOn F A)

theorem finiteUpwardHull_isIncreasing
    (F : Finset E) (A : Set (ConfigSpace E)) :
    IsIncreasing (finiteUpwardHull F A) := by
  intro eta theta heta hmem
  obtain ⟨omega, homega, hle⟩ := hmem
  exact ⟨omega, homega, fun e he => (hle e he).trans (heta e)⟩

theorem subset_finiteUpwardHull
    (F : Finset E) (A : Set (ConfigSpace E)) :
    A ⊆ finiteUpwardHull F A := by
  intro omega homega
  exact ⟨omega, homega, fun _ _ => le_rfl⟩

theorem isClosed_Iic_config (x : ConfigSpace E) :
    IsClosed (Set.Iic x) := by
  have heq : Set.Iic x = ⋂ e : E, (fun omega : ConfigSpace E => omega e) ⁻¹'
      {b : Bool | b ≤ x e} := by
    ext omega
    simp only [Set.mem_Iic, Set.mem_iInter, Set.mem_preimage,
      Set.mem_setOf_eq, Pi.le_def]
  rw [heq]
  exact isClosed_iInter fun e =>
    (isClosed_discrete {b : Bool | b ≤ x e}).preimage (continuous_apply e)

theorem finiteUpwardHull_not_mem_of_disjoint_Iic
    (F : Finset E) (A : Set (ConfigSpace E)) (x : ConfigSpace E)
    (hA : DependsOn A (F : Set E))
    (hdisjoint : Disjoint A (Set.Iic x)) :
    x ∉ finiteUpwardHull F A := by
  rintro ⟨omega, homega, hle⟩
  let rho : ConfigSpace E := fun e => if e ∈ F then omega e else false
  have hagree : agreeOn (F : Set E) omega rho := by
    intro e he
    have heF : e ∈ F := he
    simp only [rho, if_pos heF]
  have hrhoA : rho ∈ A := (hA omega rho hagree).mp homega
  have hrhole : rho ≤ x := by
    intro e
    by_cases he : e ∈ F
    · simpa only [rho, if_pos he] using hle e he
    · simp only [rho, if_neg he]
      exact Bool.false_le _
  exact Set.disjoint_left.1 hdisjoint hrhoA hrhole


theorem exists_increasing_isClopen_superset_not_mem
    (C : Set (ConfigSpace E)) (hCclosed : IsClosed C)
    (hCinc : IsIncreasing C) {x : ConfigSpace E} (hx : x ∉ C) :
    ∃ H : Set (ConfigSpace E), IsClopen H ∧ IsIncreasing H ∧
      C ⊆ H ∧ x ∉ H := by
  have hCIic : C ⊆ (Set.Iic x)ᶜ := by
    intro omega homega hle
    exact hx (hCinc hle homega)
  obtain ⟨U, hUclopen, hCU, hUsub⟩ :=
    exists_clopen_of_closed_subset_open hCclosed
      (isClosed_Iic_config x).isOpen_compl hCIic
  obtain ⟨F, hF⟩ := FK.isClopen_dependsOn_finset U hUclopen
  refine ⟨finiteUpwardHull F U, finiteUpwardHull_isClopen F U,
    finiteUpwardHull_isIncreasing F U,
    hCU.trans (subset_finiteUpwardHull F U), ?_⟩
  apply finiteUpwardHull_not_mem_of_disjoint_Iic F U x hF
  exact Set.disjoint_left.2 fun omega homega hle => hUsub homega hle


theorem exists_antitone_isClopen_isIncreasing_iInter_eq
    (C : Set (ConfigSpace E)) (hCclosed : IsClosed C)
    (hCinc : IsIncreasing C) :
    ∃ A : Nat → Set (ConfigSpace E), Antitone A ∧
      (∀ n, IsClopen (A n)) ∧ (∀ n, IsIncreasing (A n)) ∧
      (⋂ n, A n) = C := by
  classical
  by_cases hCuniv : C = Set.univ
  · refine ⟨fun _ => Set.univ, antitone_const, fun _ => isClopen_univ,
      fun _ _ _ _ _ => Set.mem_univ _, ?_⟩
    simp only [iInter_univ, hCuniv]
  have hcompl : (Cᶜ).Nonempty := Set.nonempty_compl.mpr hCuniv
  choose H hHcl hHinc hCH hxH using fun x : (Cᶜ : Set (ConfigSpace E)) =>
    exists_increasing_isClopen_superset_not_mem C hCclosed hCinc x.2
  have hunion : ⋃ x : (Cᶜ : Set (ConfigSpace E)), (H x)ᶜ = Cᶜ := by
    apply Set.Subset.antisymm
    · intro omega homega
      obtain ⟨x, hx⟩ := Set.mem_iUnion.1 homega
      exact fun homegaC => hx (hCH x homegaC)
    · intro omega homega
      exact Set.mem_iUnion.2 ⟨⟨omega, homega⟩, hxH ⟨omega, homega⟩⟩
  obtain ⟨T, hTcount, hTunion⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : (Cᶜ : Set (ConfigSpace E)) => (H x)ᶜ)
      (fun x => (hHcl x).compl.isOpen)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hselected : (⋃ x ∈ T, (H x)ᶜ) = ∅ := by
      rw [hTempty]
      simp
    have hfull : (⋃ x : (Cᶜ : Set (ConfigSpace E)), (H x)ᶜ) = ∅ := by
      rw [← hTunion, hselected]
    exact hcompl.ne_empty (by rw [← hunion]; exact hfull)
  obtain ⟨f, hf⟩ := Set.Countable.exists_surjective hTnonempty hTcount
  let A : Nat → Set (ConfigSpace E) := fun n =>
    ⋂ i : Fin (n + 1), H (f i).1
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro n m hnm omega homega
    simp only [A, Set.mem_iInter] at homega ⊢
    intro i
    exact homega ⟨i.1, lt_of_lt_of_le i.2 (Nat.add_le_add_right hnm 1)⟩
  · intro n
    exact isClopen_iInter_of_finite fun i => hHcl (f i).1
  · intro n omega eta hle homega
    simp only [A, Set.mem_iInter] at homega ⊢
    intro i
    exact hHinc (f i).1 hle (homega i)
  · ext omega
    simp only [Set.mem_iInter]
    constructor
    · intro homega
      by_contra hnot
      have hcomp : omega ∈ Cᶜ := hnot
      have hcovered : omega ∈ ⋃ x ∈ T, (H x)ᶜ := by
        rw [hTunion, hunion]
        exact hcomp
      obtain ⟨x, hx⟩ := Set.mem_iUnion.1 hcovered
      obtain ⟨hxT, hxH'⟩ := Set.mem_iUnion.1 hx
      obtain ⟨k, hk⟩ := hf ⟨x, hxT⟩
      have hkA := homega k
      simp only [A, Set.mem_iInter] at hkA
      have hmem := hkA ⟨k, Nat.lt_succ_self k⟩
      exact hxH' (by simpa only [hk] using hmem)
    · intro homega n
      simp only [A, Set.mem_iInter]
      intro i
      exact hCH (f i).1 homega


end StatMech
