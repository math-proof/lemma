import Mathlib
import sympy.Basic
import Def.InformationTheory.Shearer
open Finset BigOperators Real
open MathlibExt.InformationTheory.Shearer


namespace MathlibExt.InformationTheory.Shearer

/--
[shearerMarginal_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
lemma shearerMarginal_nonneg
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {S : Finset (Fin n)}
  {y : ↥S → α}
-- given
  (hμ : ∀ x, 0 ≤ μ x) :
-- imply
  0 ≤ shearerMarginal μ S y := by
-- proof
  unfold shearerMarginal
  apply Finset.sum_nonneg
  intro x _
  split_ifs with h
  · exact hμ x
  · exact le_refl 0

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerMarginal_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
lemma shearerMarginal_sum
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {S : Finset (Fin n)}
-- given
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1) :
-- imply
  ∑ y : (↥S → α), shearerMarginal μ S y = 1 := by
-- proof
  unfold shearerMarginal
  conv_rhs => rw [← hμ_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[gibbs_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma gibbs_ineq {β : Type*} [Fintype β]
  (p q : β → ℝ) (hp : ∀ b, 0 ≤ p b) (hq : ∀ b, 0 ≤ q b)
  (hp_sum : ∑ b, p b = 1) (hq_sum : ∑ b, q b = 1)
  (hsupp : ∀ b, p b ≠ 0 → q b ≠ 0) :
  -∑ b, p b * Real.log (p b) ≤ -∑ b, p b * Real.log (q b) := by
  have hpoint : ∀ b, p b * Real.log (q b / p b)
    = p b * Real.log (q b) - p b * Real.log (p b) := by
    intro b
    by_cases h : p b = 0
    · simp [h]
    · have hqne : q b ≠ 0 := hsupp b h
      rw [Real.log_div hqne h, mul_sub]
  have hbound : ∀ b, p b * Real.log (q b / p b) ≤ q b - p b := by
    intro b
    by_cases h : p b = 0
    · rw [h, zero_mul]
      simp only [sub_zero]
      exact hq b
    · have hpos : 0 < p b := lt_of_le_of_ne (hp b) (Ne.symm h)
      have hqne : q b ≠ 0 := hsupp b h
      have hqpos : 0 < q b := lt_of_le_of_ne (hq b) (Ne.symm hqne)
      have hdiv : 0 < q b / p b := div_pos hqpos hpos
      have hlog := Real.log_le_sub_one_of_pos hdiv
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
      have hcalc : p b * (q b / p b - 1) = q b - p b := by
        field_simp
      rwa [hcalc] at hmul
  have hle : ∑ b, p b * Real.log (q b / p b) ≤ 0 := by
    calc ∑ b, p b * Real.log (q b / p b)
      ≤ ∑ b, (q b - p b) := Finset.sum_le_sum (fun b _ => hbound b)
      _ = 0 := by rw [Finset.sum_sub_distrib, hq_sum, hp_sum, sub_self]
  have heq : ∑ b, p b * Real.log (q b / p b)
    = (∑ b, p b * Real.log (q b)) - ∑ b, p b * Real.log (p b) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    exact hpoint b
  rw [heq] at hle
  linarith

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[sum_fiber_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma sum_fiber_mul {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq γ]
  (f : β → γ) (w : β → ℝ) (g : γ → ℝ) :
  ∑ z : γ, (∑ x : β, if f x = z then w x else 0) * g z
    = ∑ x : β, w x * g (f x) := by
  have hpush : ∀ z : γ, (∑ x : β, if f x = z then w x else 0) * g z
    = ∑ x : β, (if f x = z then w x * g z else 0) := by
    intro z
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : f x = z <;> simp [h]
  calc ∑ z : γ, (∑ x : β, if f x = z then w x else 0) * g z
    = ∑ z : γ, ∑ x : β, (if f x = z then w x * g z else 0) :=
      Finset.sum_congr rfl (fun z _ => hpush z)
    _ = ∑ x : β, ∑ z : γ, (if f x = z then w x * g z else 0) :=
      Finset.sum_comm
    _ = ∑ x : β, w x * g (f x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[sum_tower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma sum_tower {β γ δ : Type*} [Fintype β] [Fintype γ]
  [DecidableEq γ] [DecidableEq δ]
  (g : β → γ) (f : γ → δ) (w : β → ℝ) (z : δ) :
  (∑ x : β, if f (g x) = z then w x else 0)
    = ∑ y : γ, if f y = z then (∑ x : β, if g x = y then w x else 0) else 0 := by
  have hdist : ∀ y : γ, (if f y = z then (∑ x : β, if g x = y then w x else 0) else 0)
    = ∑ x : β, (if f y = z then (if g x = y then w x else 0) else 0) := by
    intro y
    by_cases h : f y = z <;> simp [h]
  have hinner : ∀ x : β, (∑ y : γ, (if f y = z then (if g x = y then w x else 0) else 0))
    = (if f (g x) = z then w x else 0) := by
    intro x
    have hswap : ∀ y : γ, (if f y = z then (if g x = y then w x else 0) else 0)
      = (if g x = y then (if f y = z then w x else 0) else 0) := by
      intro y
      by_cases h1 : f y = z <;> by_cases h2 : g x = y <;> simp_all
    calc (∑ y : γ, (if f y = z then (if g x = y then w x else 0) else 0))
      = ∑ y : γ, (if g x = y then (if f y = z then w x else 0) else 0) :=
        Finset.sum_congr rfl (fun y _ => hswap y)
      _ = (if f (g x) = z then w x else 0) := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  calc (∑ x : β, if f (g x) = z then w x else 0)
    = ∑ x : β, ∑ y : γ, (if f y = z then (if g x = y then w x else 0) else 0) :=
      Finset.sum_congr rfl (fun x _ => (hinner x).symm)
    _ = ∑ y : γ, ∑ x : β, (if f y = z then (if g x = y then w x else 0) else 0) :=
      Finset.sum_comm
    _ = ∑ y : γ, if f y = z then (∑ x : β, if g x = y then w x else 0) else 0 :=
      Finset.sum_congr rfl (fun y _ => (hdist y).symm)

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerMarginal_tower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerMarginal_tower {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
  (μ : (Fin n → α) → ℝ) (S T : Finset (Fin n)) (hTS : T ⊆ S) (z : ↥T → α) :
  shearerMarginal μ T z
    = ∑ y : (↥S → α), if (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z then
      shearerMarginal μ S y else 0 := by
  have hcomp : ∀ x : (Fin n → α),
    (fun t : ↥T => (fun s : ↥S => x s.val) ⟨t.val, hTS t.property⟩)
      = (fun s : ↥T => x s.val) := fun x => rfl
  unfold shearerMarginal
  refine Eq.trans ?_ (sum_tower _ _ μ z)
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hcomp x]

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerMarginalEntropy_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
lemma shearerMarginalEntropy_mono
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {S T : Finset (Fin n)}
-- given
  (hμ : ∀ x, 0 ≤ μ x)
  (hTS : T ⊆ S) :
-- imply
  shearerMarginalEntropy μ T ≤ shearerMarginalEntropy μ S := by
-- proof
  have hPSnn : ∀ y : (↥S → α), 0 ≤ shearerMarginal μ S y :=
    fun y => shearerMarginal_nonneg μ hμ S y
  have hsplit : (∑ y : (↥S → α), shearerMarginal μ S y * Real.log (shearerMarginal μ S y))
    = ∑ z : (↥T → α), ∑ y : (↥S → α),
      (if (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z
        then shearerMarginal μ S y * Real.log (shearerMarginal μ S y) else 0) := by
    calc (∑ y : (↥S → α), shearerMarginal μ S y * Real.log (shearerMarginal μ S y))
      = ∑ y : (↥S → α), ∑ z : (↥T → α),
        (if (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z
          then shearerMarginal μ S y * Real.log (shearerMarginal μ S y) else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_ite_eq]
        simp
      _ = ∑ z : (↥T → α), ∑ y : (↥S → α),
        (if (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z
          then shearerMarginal μ S y * Real.log (shearerMarginal μ S y) else 0) :=
        Finset.sum_comm
  have hper : ∀ z : (↥T → α),
    (∑ y : (↥S → α), (if (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z
      then shearerMarginal μ S y * Real.log (shearerMarginal μ S y) else 0))
    ≤ shearerMarginal μ T z * Real.log (shearerMarginal μ T z) := by
    intro z
    have hle : ∀ y : (↥S → α),
      (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z →
      shearerMarginal μ S y ≤ shearerMarginal μ T z := by
      intro y hyz
      calc shearerMarginal μ S y
        = (if (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z
          then shearerMarginal μ S y else 0) := by simp [hyz]
        _ ≤ ∑ y' : (↥S → α), (if (fun t : ↥T => y' ⟨t.val, hTS t.property⟩) = z
          then shearerMarginal μ S y' else 0) := by
          apply Finset.single_le_sum _ (Finset.mem_univ y)
          intro i _
          split_ifs with h
          · exact hPSnn i
          · exact le_refl 0
        _ = shearerMarginal μ T z := (shearerMarginal_tower μ S T hTS z).symm
    have hper_y : ∀ y : (↥S → α),
      (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z →
      shearerMarginal μ S y * Real.log (shearerMarginal μ S y)
      ≤ shearerMarginal μ S y * Real.log (shearerMarginal μ T z) := by
      intro y hyz
      have hle' : shearerMarginal μ S y ≤ shearerMarginal μ T z := hle y hyz
      by_cases h0 : shearerMarginal μ S y = 0
      · rw [h0]
        simp
      · have hpos : 0 < shearerMarginal μ S y :=
        lt_of_le_of_ne (hPSnn y) (Ne.symm h0)
        have hlog : Real.log (shearerMarginal μ S y) ≤ Real.log (shearerMarginal μ T z) :=
          Real.log_le_log hpos hle'
        exact mul_le_mul_of_nonneg_left hlog (hPSnn y)
    have hexpand : shearerMarginal μ T z * Real.log (shearerMarginal μ T z)
      = ∑ y : (↥S → α), (if (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z
        then shearerMarginal μ S y * Real.log (shearerMarginal μ T z) else 0) := by
      rw [shearerMarginal_tower μ S T hTS z, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : (fun t : ↥T => y ⟨t.val, hTS t.property⟩) = z <;> simp [h]
    rw [hexpand]
    apply Finset.sum_le_sum
    intro y _
    split_ifs with h
    · exact hper_y y h
    · exact le_refl 0
  unfold shearerMarginalEntropy
  rw [hsplit]
  apply neg_le_neg
  exact Finset.sum_le_sum (fun z _ => hper z)

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[fiber_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma fiber_le {β γ : Type*} [Fintype β] [DecidableEq γ]
  (f : β → γ) (w : β → ℝ) (hw : ∀ x, 0 ≤ w x) (x : β) (z : γ) (h : f x = z) :
  w x ≤ ∑ y : β, if f y = z then w y else 0 := by
  calc w x = (if f x = z then w x else 0) := by simp [h]
    _ ≤ (∑ y : β, if f y = z then w y else 0) := by
      apply Finset.single_le_sum _ (Finset.mem_univ x)
      intro i _
      split_ifs with hh
      · exact hw i
      · exact le_refl 0

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerGlue_fst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerGlue_fst {n : ℕ} {α : Type*} (A B : Finset (Fin n))
  (u : ↥A → α) (v : ↥B → α) :
  shearerResL A B (shearerGlue A B u v) = u := by
  funext m
  simp only [shearerResL, shearerGlue]
  split_ifs with h
  · rfl
  · exact False.elim (h m.property)

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerGlue_snd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerGlue_snd {n : ℕ} {α : Type*} (A B : Finset (Fin n))
  (u : ↥A → α) (v : ↥B → α) (t : ↥(A ∩ B) → α)
  (hu : shearerResDL A B u = t) (hv : shearerResDR A B v = t) :
  shearerResR A B (shearerGlue A B u v) = v := by
  funext m
  simp only [shearerResR, shearerGlue]
  split_ifs with h
  · calc u ⟨m.val, h⟩
    = shearerResDL A B u ⟨m.val, Finset.mem_inter.mpr ⟨h, m.property⟩⟩ := rfl
    _ = t ⟨m.val, Finset.mem_inter.mpr ⟨h, m.property⟩⟩ := by rw [hu]
    _ = shearerResDR A B v ⟨m.val, Finset.mem_inter.mpr ⟨h, m.property⟩⟩ := by rw [hv]
    _ = v m := rfl
  · rfl

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerGlue_mid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerGlue_mid {n : ℕ} {α : Type*} (A B : Finset (Fin n))
  (u : ↥A → α) (v : ↥B → α) (t : ↥(A ∩ B) → α)
  (hu : shearerResDL A B u = t) :
  shearerResI A B (shearerGlue A B u v) = t := by
  funext m
  have hmA : m.val ∈ A := (Finset.mem_inter.mp m.property).1
  simp only [shearerResI, shearerGlue]
  simp only [hmA, ↓reduceDIte]
  calc u ⟨m.val, hmA⟩ = shearerResDL A B u m := rfl
    _ = t m := by rw [hu]

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerMarginalEntropy_submodular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
lemma shearerMarginalEntropy_submodular
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {A B : Finset (Fin n)}
-- given
  (hμ : ∀ x, 0 ≤ μ x)
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1) :
-- imply
  shearerMarginalEntropy μ (A ∪ B) + shearerMarginalEntropy μ (A ∩ B)
    ≤ shearerMarginalEntropy μ A + shearerMarginalEntropy μ B := by
-- proof
  have hPnn : ∀ z : ↥(A ∪ B) → α, 0 ≤ shearerMarginal μ (A ∪ B) z :=
    fun z => shearerMarginal_nonneg μ hμ (A ∪ B) z
  have hPAnn : ∀ u : ↥A → α, 0 ≤ shearerMarginal μ A u :=
    fun u => shearerMarginal_nonneg μ hμ A u
  have hPBnn : ∀ v : ↥B → α, 0 ≤ shearerMarginal μ B v :=
    fun v => shearerMarginal_nonneg μ hμ B v
  have hPCnn : ∀ t : ↥(A ∩ B) → α, 0 ≤ shearerMarginal μ (A ∩ B) t :=
    fun t => shearerMarginal_nonneg μ hμ (A ∩ B) t
  have hPA : ∀ u : ↥A → α, shearerMarginal μ A u
    = ∑ z : ↥(A ∪ B) → α, if shearerResL A B z = u then shearerMarginal μ (A ∪ B) z else 0 :=
    fun u => shearerMarginal_tower μ (A ∪ B) A Finset.subset_union_left u
  have hPB : ∀ v : ↥B → α, shearerMarginal μ B v
    = ∑ z : ↥(A ∪ B) → α, if shearerResR A B z = v then shearerMarginal μ (A ∪ B) z else 0 :=
    fun v => shearerMarginal_tower μ (A ∪ B) B Finset.subset_union_right v
  have hPC : ∀ t : ↥(A ∩ B) → α, shearerMarginal μ (A ∩ B) t
    = ∑ z : ↥(A ∪ B) → α, if shearerResI A B z = t then shearerMarginal μ (A ∪ B) z else 0 :=
    fun t => shearerMarginal_tower μ (A ∪ B) (A ∩ B)
      (fun x hx => Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hx).1)) t
  have hPCA : ∀ t : ↥(A ∩ B) → α, shearerMarginal μ (A ∩ B) t
    = ∑ u : ↥A → α, if shearerResDL A B u = t then shearerMarginal μ A u else 0 :=
    fun t => shearerMarginal_tower μ A (A ∩ B) Finset.inter_subset_left t
  have hPCB : ∀ t : ↥(A ∩ B) → α, shearerMarginal μ (A ∩ B) t
    = ∑ v : ↥B → α, if shearerResDR A B v = t then shearerMarginal μ B v else 0 :=
    fun t => shearerMarginal_tower μ B (A ∩ B) Finset.inter_subset_right t
  have hda : ∀ z : ↥(A ∪ B) → α,
    shearerResDL A B (shearerResL A B z) = shearerResI A B z := fun z => rfl
  have heb : ∀ z : ↥(A ∪ B) → α,
    shearerResDR A B (shearerResR A B z) = shearerResI A B z := fun z => rfl
  have hPsum : ∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z = 1 :=
    shearerMarginal_sum μ hμ_sum (A ∪ B)
  have hbij : ∀ t : ↥(A ∩ B) → α,
    (∑ z ∈ Finset.univ.filter (fun z : ↥(A ∪ B) → α => shearerResI A B z = t),
      shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z))
    = ∑ p ∈ (Finset.univ.filter (fun u : ↥A → α => shearerResDL A B u = t)) ×ˢ
      (Finset.univ.filter (fun v : ↥B → α => shearerResDR A B v = t)),
      shearerMarginal μ A p.1 * shearerMarginal μ B p.2 := by
    intro t
    refine Finset.sum_bij (fun z _ => (shearerResL A B z, shearerResR A B z)) ?_ ?_ ?_ ?_
    · intro z hz
      show (shearerResL A B z, shearerResR A B z) ∈
        (Finset.univ.filter (fun u : ↥A → α => shearerResDL A B u = t)) ×ˢ
        (Finset.univ.filter (fun v : ↥B → α => shearerResDR A B v = t))
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_⟩, ⟨Finset.mem_univ _, ?_⟩⟩
      · change shearerResDL A B (shearerResL A B z) = t
        rw [hda z]
        exact (Finset.mem_filter.mp hz).2
      · change shearerResDR A B (shearerResR A B z) = t
        rw [heb z]
        exact (Finset.mem_filter.mp hz).2
    · intro z₁ _ z₂ _ hzz
      have hzz' : (shearerResL A B z₁, shearerResR A B z₁)
        = (shearerResL A B z₂, shearerResR A B z₂) := hzz
      rw [Prod.mk.injEq] at hzz'
      obtain ⟨ha, hb⟩ := hzz'
      funext s
      obtain hA | hB := Finset.mem_union.mp s.property
      · calc z₁ s = shearerResL A B z₁ ⟨s.val, hA⟩ := rfl
        _ = shearerResL A B z₂ ⟨s.val, hA⟩ := by rw [ha]
        _ = z₂ s := rfl
      · calc z₁ s = shearerResR A B z₁ ⟨s.val, hB⟩ := rfl
        _ = shearerResR A B z₂ ⟨s.val, hB⟩ := by rw [hb]
        _ = z₂ s := rfl
    · intro q hq
      obtain ⟨u, v⟩ := q
      have hu : shearerResDL A B u = t :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
      have hv : shearerResDR A B v = t :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
      refine ⟨shearerGlue A B u v, ?_, ?_⟩
      · show shearerGlue A B u v
        ∈ Finset.univ.filter (fun z : ↥(A ∪ B) → α => shearerResI A B z = t)
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        show shearerResI A B (shearerGlue A B u v) = t
        exact shearerGlue_mid A B u v t hu
      · show (shearerResL A B (shearerGlue A B u v),
        shearerResR A B (shearerGlue A B u v)) = (u, v)
        rw [Prod.mk.injEq]
        exact ⟨shearerGlue_fst A B u v, shearerGlue_snd A B u v t hu hv⟩
    · intro z hz
      rfl
  have hprod2 : ∀ t : ↥(A ∩ B) → α,
    (∑ p ∈ (Finset.univ.filter (fun u : ↥A → α => shearerResDL A B u = t)) ×ˢ
      (Finset.univ.filter (fun v : ↥B → α => shearerResDR A B v = t)),
      shearerMarginal μ A p.1 * shearerMarginal μ B p.2)
    = (∑ u ∈ Finset.univ.filter (fun u : ↥A → α => shearerResDL A B u = t),
      shearerMarginal μ A u)
      * (∑ v ∈ Finset.univ.filter (fun v : ↥B → α => shearerResDR A B v = t),
        shearerMarginal μ B v) := by
    intro t
    rw [Finset.sum_product]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  have hFL : ∀ t : ↥(A ∩ B) → α,
    (∑ z : ↥(A ∪ B) → α, if shearerResI A B z = t
      then shearerMarginal μ A (shearerResL A B z) *
        shearerMarginal μ B (shearerResR A B z) else 0)
    = shearerMarginal μ (A ∩ B) t * shearerMarginal μ (A ∩ B) t := by
    intro t
    have hfilter : (∑ z : ↥(A ∪ B) → α, if shearerResI A B z = t
      then shearerMarginal μ A (shearerResL A B z) *
        shearerMarginal μ B (shearerResR A B z) else 0)
      = ∑ z ∈ Finset.univ.filter (fun z : ↥(A ∪ B) → α => shearerResI A B z = t),
        shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z) :=
      (Finset.sum_filter (fun z : ↥(A ∪ B) → α => shearerResI A B z = t)
        (fun z : ↥(A ∪ B) → α => shearerMarginal μ A (shearerResL A B z)
          * shearerMarginal μ B (shearerResR A B z))).symm
    have gA : (∑ u ∈ Finset.univ.filter (fun u : ↥A → α => shearerResDL A B u = t),
      shearerMarginal μ A u) = shearerMarginal μ (A ∩ B) t := by
      have hfilterA : (∑ u : ↥A → α, if shearerResDL A B u = t then shearerMarginal μ A u else 0)
        = ∑ u ∈ Finset.univ.filter (fun u : ↥A → α => shearerResDL A B u = t),
          shearerMarginal μ A u :=
        (Finset.sum_filter (fun u : ↥A → α => shearerResDL A B u = t)
          (fun u : ↥A → α => shearerMarginal μ A u)).symm
      rw [← hfilterA]
      exact (hPCA t).symm
    have gB : (∑ v ∈ Finset.univ.filter (fun v : ↥B → α => shearerResDR A B v = t),
      shearerMarginal μ B v) = shearerMarginal μ (A ∩ B) t := by
      have hfilterB : (∑ v : ↥B → α, if shearerResDR A B v = t then shearerMarginal μ B v else 0)
        = ∑ v ∈ Finset.univ.filter (fun v : ↥B → α => shearerResDR A B v = t),
          shearerMarginal μ B v :=
        (Finset.sum_filter (fun v : ↥B → α => shearerResDR A B v = t)
          (fun v : ↥B → α => shearerMarginal μ B v)).symm
      rw [← hfilterB]
      exact (hPCB t).symm
    rw [hfilter, hbij t, hprod2 t, gA, gB]
  have hQnn : ∀ z : ↥(A ∪ B) → α, 0 ≤ shearerQ μ A B z := by
    intro z
    have hQeq : shearerQ μ A B z
      = (if shearerMarginal μ (A ∩ B) (shearerResI A B z) = 0 then (0 : ℝ)
        else shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z)
          / shearerMarginal μ (A ∩ B) (shearerResI A B z)) := rfl
    rw [hQeq]
    split_ifs with h
    · exact le_refl 0
    · exact div_nonneg (mul_nonneg (hPAnn _) (hPBnn _))
      (le_of_lt (lt_of_le_of_ne (hPCnn _) (Ne.symm h)))
  have hinnerQ : ∀ t : ↥(A ∩ B) → α,
    (∑ z : ↥(A ∪ B) → α, if shearerResI A B z = t then shearerQ μ A B z else 0)
    = shearerMarginal μ (A ∩ B) t := by
    intro t
    by_cases ht : shearerMarginal μ (A ∩ B) t = 0
    · calc (∑ z : ↥(A ∪ B) → α, if shearerResI A B z = t then shearerQ μ A B z else 0)
      = ∑ z : ↥(A ∪ B) → α, (0 : ℝ) := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases h : shearerResI A B z = t
        · have h0 : shearerMarginal μ (A ∩ B) (shearerResI A B z) = 0 := by
          rwa [h]
          have hQ0 : shearerQ μ A B z = 0 := by
            unfold shearerQ
            simp [h0]
          simp [h, hQ0]
        · simp [h]
      _ = 0 := Finset.sum_const_zero
      _ = shearerMarginal μ (A ∩ B) t := ht.symm
    · have hterm : ∀ z : ↥(A ∪ B) → α,
      (if shearerResI A B z = t then shearerQ μ A B z else 0)
      = (if shearerResI A B z = t
        then shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z)
          / shearerMarginal μ (A ∩ B) t else 0) := by
      intro z
      by_cases h : shearerResI A B z = t
      · have h0 : shearerMarginal μ (A ∩ B) (shearerResI A B z)
        = shearerMarginal μ (A ∩ B) t := by rw [h]
        have hne : shearerMarginal μ (A ∩ B) (shearerResI A B z) ≠ 0 := by
          rwa [h0]
        have hQeq : shearerQ μ A B z
          = shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z)
            / shearerMarginal μ (A ∩ B) t := by
          have hQeq2 : shearerQ μ A B z
            = shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z)
              / shearerMarginal μ (A ∩ B) (shearerResI A B z) := by
            unfold shearerQ
            simp [hne]
          rw [hQeq2, h0]
        simp [h, hQeq]
      · simp [h]
      have hpush : ∀ z : ↥(A ∪ B) → α,
        (if shearerResI A B z = t
          then shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z)
            / shearerMarginal μ (A ∩ B) t else 0)
        = ((if shearerResI A B z = t
          then shearerMarginal μ A (shearerResL A B z) *
            shearerMarginal μ B (shearerResR A B z) else 0)
          / shearerMarginal μ (A ∩ B) t) := by
        intro z
        split_ifs with h
        · rfl
        · simp
      calc (∑ z : ↥(A ∪ B) → α, if shearerResI A B z = t then shearerQ μ A B z else 0)
        = ∑ z : ↥(A ∪ B) → α, (if shearerResI A B z = t
          then shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z)
            / shearerMarginal μ (A ∩ B) t else 0) :=
          Finset.sum_congr rfl (fun z _ => hterm z)
        _ = ∑ z : ↥(A ∪ B) → α, (((if shearerResI A B z = t
          then shearerMarginal μ A (shearerResL A B z) *
            shearerMarginal μ B (shearerResR A B z) else 0))
          / shearerMarginal μ (A ∩ B) t) :=
          Finset.sum_congr rfl (fun z _ => hpush z)
        _ = (∑ z : ↥(A ∪ B) → α, (if shearerResI A B z = t
          then shearerMarginal μ A (shearerResL A B z) *
            shearerMarginal μ B (shearerResR A B z) else 0))
          / shearerMarginal μ (A ∩ B) t := by
          simp only [div_eq_mul_inv, ← Finset.sum_mul]
        _ = shearerMarginal μ (A ∩ B) t * shearerMarginal μ (A ∩ B) t
          / shearerMarginal μ (A ∩ B) t := by
          rw [hFL t]
        _ = shearerMarginal μ (A ∩ B) t := by
          field_simp
  have hQsum : ∑ z : ↥(A ∪ B) → α, shearerQ μ A B z = 1 := by
    have hstep : ∀ z : ↥(A ∪ B) → α, shearerQ μ A B z
      = ∑ t : ↥(A ∩ B) → α, (if shearerResI A B z = t then shearerQ μ A B z else 0) := by
      intro z
      rw [Finset.sum_ite_eq]
      simp
    calc ∑ z : ↥(A ∪ B) → α, shearerQ μ A B z
      = ∑ z : ↥(A ∪ B) → α, ∑ t : ↥(A ∩ B) → α,
        (if shearerResI A B z = t then shearerQ μ A B z else 0) :=
        Finset.sum_congr rfl (fun z _ => hstep z)
      _ = ∑ t : ↥(A ∩ B) → α, ∑ z : ↥(A ∪ B) → α,
        (if shearerResI A B z = t then shearerQ μ A B z else 0) := Finset.sum_comm
      _ = ∑ t : ↥(A ∩ B) → α, shearerMarginal μ (A ∩ B) t := by
        apply Finset.sum_congr rfl
        intro t _
        exact hinnerQ t
      _ = 1 := shearerMarginal_sum μ hμ_sum (A ∩ B)
  have hsupp : ∀ z : ↥(A ∪ B) → α,
    shearerMarginal μ (A ∪ B) z ≠ 0 → shearerQ μ A B z ≠ 0 := by
    intro z hz
    have hpos : 0 < shearerMarginal μ (A ∪ B) z :=
      lt_of_le_of_ne (hPnn z) (Ne.symm hz)
    have hA : shearerMarginal μ A (shearerResL A B z) ≠ 0 := by
      have hle : shearerMarginal μ (A ∪ B) z ≤ shearerMarginal μ A (shearerResL A B z) := by
        calc shearerMarginal μ (A ∪ B) z
          ≤ (∑ y : ↥(A ∪ B) → α, if shearerResL A B y = shearerResL A B z
            then shearerMarginal μ (A ∪ B) y else 0) :=
            fiber_le _ _ hPnn z _ rfl
          _ = shearerMarginal μ A (shearerResL A B z) := (hPA _).symm
      exact ne_of_gt (lt_of_lt_of_le hpos hle)
    have hB : shearerMarginal μ B (shearerResR A B z) ≠ 0 := by
      have hle : shearerMarginal μ (A ∪ B) z ≤ shearerMarginal μ B (shearerResR A B z) := by
        calc shearerMarginal μ (A ∪ B) z
          ≤ (∑ y : ↥(A ∪ B) → α, if shearerResR A B y = shearerResR A B z
            then shearerMarginal μ (A ∪ B) y else 0) :=
            fiber_le _ _ hPnn z _ rfl
          _ = shearerMarginal μ B (shearerResR A B z) := (hPB _).symm
      exact ne_of_gt (lt_of_lt_of_le hpos hle)
    have hC : shearerMarginal μ (A ∩ B) (shearerResI A B z) ≠ 0 := by
      have hle : shearerMarginal μ (A ∪ B) z ≤ shearerMarginal μ (A ∩ B) (shearerResI A B z) := by
        calc shearerMarginal μ (A ∪ B) z
          ≤ (∑ y : ↥(A ∪ B) → α, if shearerResI A B y = shearerResI A B z
            then shearerMarginal μ (A ∪ B) y else 0) :=
            fiber_le _ _ hPnn z _ rfl
          _ = shearerMarginal μ (A ∩ B) (shearerResI A B z) := (hPC _).symm
      exact ne_of_gt (lt_of_lt_of_le hpos hle)
    have hQeq : shearerQ μ A B z
      = shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z)
        / shearerMarginal μ (A ∩ B) (shearerResI A B z) := by
      unfold shearerQ
      simp [hC]
    rw [hQeq]
    exact div_ne_zero (mul_ne_zero hA hB) hC
  have reindexA : (∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z
    * Real.log (shearerMarginal μ A (shearerResL A B z)))
    = ∑ u : ↥A → α, shearerMarginal μ A u * Real.log (shearerMarginal μ A u) := by
    calc (∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z
      * Real.log (shearerMarginal μ A (shearerResL A B z)))
      = ∑ u : ↥A → α, (∑ x : ↥(A ∪ B) → α, if shearerResL A B x = u
        then shearerMarginal μ (A ∪ B) x else 0) * Real.log (shearerMarginal μ A u) := by
        exact (sum_fiber_mul (shearerResL A B) (shearerMarginal μ (A ∪ B))
          (fun u => Real.log (shearerMarginal μ A u))).symm
      _ = ∑ u : ↥A → α, shearerMarginal μ A u * Real.log (shearerMarginal μ A u) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [← hPA u]
  have reindexB : (∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z
    * Real.log (shearerMarginal μ B (shearerResR A B z)))
    = ∑ v : ↥B → α, shearerMarginal μ B v * Real.log (shearerMarginal μ B v) := by
    calc (∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z
      * Real.log (shearerMarginal μ B (shearerResR A B z)))
      = ∑ v : ↥B → α, (∑ x : ↥(A ∪ B) → α, if shearerResR A B x = v
        then shearerMarginal μ (A ∪ B) x else 0) * Real.log (shearerMarginal μ B v) := by
        exact (sum_fiber_mul (shearerResR A B) (shearerMarginal μ (A ∪ B))
          (fun v => Real.log (shearerMarginal μ B v))).symm
      _ = ∑ v : ↥B → α, shearerMarginal μ B v * Real.log (shearerMarginal μ B v) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [← hPB v]
  have reindexC : (∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z
    * Real.log (shearerMarginal μ (A ∩ B) (shearerResI A B z)))
    = ∑ t : ↥(A ∩ B) → α, shearerMarginal μ (A ∩ B) t
      * Real.log (shearerMarginal μ (A ∩ B) t) := by
    calc (∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z
      * Real.log (shearerMarginal μ (A ∩ B) (shearerResI A B z)))
      = ∑ t : ↥(A ∩ B) → α, (∑ x : ↥(A ∪ B) → α, if shearerResI A B x = t
        then shearerMarginal μ (A ∪ B) x else 0)
        * Real.log (shearerMarginal μ (A ∩ B) t) := by
        exact (sum_fiber_mul (shearerResI A B) (shearerMarginal μ (A ∪ B))
          (fun t => Real.log (shearerMarginal μ (A ∩ B) t))).symm
      _ = ∑ t : ↥(A ∩ B) → α, shearerMarginal μ (A ∩ B) t
        * Real.log (shearerMarginal μ (A ∩ B) t) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← hPC t]
  have hlogQ : (∑ z : ↥(A ∪ B) → α,
    shearerMarginal μ (A ∪ B) z * Real.log (shearerQ μ A B z))
    = (∑ u : ↥A → α, shearerMarginal μ A u * Real.log (shearerMarginal μ A u))
      + (∑ v : ↥B → α, shearerMarginal μ B v * Real.log (shearerMarginal μ B v))
      - (∑ t : ↥(A ∩ B) → α, shearerMarginal μ (A ∩ B) t
        * Real.log (shearerMarginal μ (A ∩ B) t)) := by
    have hpoint : ∀ z : ↥(A ∪ B) → α,
      shearerMarginal μ (A ∪ B) z * Real.log (shearerQ μ A B z)
      = shearerMarginal μ (A ∪ B) z * Real.log (shearerMarginal μ A (shearerResL A B z))
        + shearerMarginal μ (A ∪ B) z * Real.log (shearerMarginal μ B (shearerResR A B z))
        - shearerMarginal μ (A ∪ B) z
          * Real.log (shearerMarginal μ (A ∩ B) (shearerResI A B z)) := by
      intro z
      by_cases hCz : shearerMarginal μ (A ∩ B) (shearerResI A B z) = 0
      · have hle : shearerMarginal μ (A ∪ B) z
        ≤ shearerMarginal μ (A ∩ B) (shearerResI A B z) := by
        calc shearerMarginal μ (A ∪ B) z
          ≤ (∑ y : ↥(A ∪ B) → α, if shearerResI A B y = shearerResI A B z
            then shearerMarginal μ (A ∪ B) y else 0) :=
            fiber_le _ _ hPnn z _ rfl
          _ = shearerMarginal μ (A ∩ B) (shearerResI A B z) := (hPC _).symm
        have hPz : shearerMarginal μ (A ∪ B) z = 0 := by
          rw [hCz] at hle
          exact le_antisymm hle (hPnn z)
        rw [hPz]
        simp
      · have hQeq : shearerQ μ A B z
        = shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z)
          / shearerMarginal μ (A ∩ B) (shearerResI A B z) := by
        unfold shearerQ
        simp [hCz]
        by_cases hPz : shearerMarginal μ (A ∪ B) z = 0
        · rw [hPz]
          simp
        · have hplt : 0 < shearerMarginal μ (A ∪ B) z :=
          lt_of_le_of_ne (hPnn z) (Ne.symm hPz)
          have hAle : shearerMarginal μ (A ∪ B) z
            ≤ shearerMarginal μ A (shearerResL A B z) := by
            calc shearerMarginal μ (A ∪ B) z
              ≤ (∑ y : ↥(A ∪ B) → α, if shearerResL A B y = shearerResL A B z
                then shearerMarginal μ (A ∪ B) y else 0) :=
                fiber_le _ _ hPnn z _ rfl
              _ = shearerMarginal μ A (shearerResL A B z) := (hPA _).symm
          have hBle : shearerMarginal μ (A ∪ B) z
            ≤ shearerMarginal μ B (shearerResR A B z) := by
            calc shearerMarginal μ (A ∪ B) z
              ≤ (∑ y : ↥(A ∪ B) → α, if shearerResR A B y = shearerResR A B z
                then shearerMarginal μ (A ∪ B) y else 0) :=
                fiber_le _ _ hPnn z _ rfl
              _ = shearerMarginal μ B (shearerResR A B z) := (hPB _).symm
          have hA : shearerMarginal μ A (shearerResL A B z) ≠ 0 :=
            ne_of_gt (lt_of_lt_of_le hplt hAle)
          have hB : shearerMarginal μ B (shearerResR A B z) ≠ 0 :=
            ne_of_gt (lt_of_lt_of_le hplt hBle)
          have hAmul : shearerMarginal μ A (shearerResL A B z)
            * shearerMarginal μ B (shearerResR A B z) ≠ 0 :=
            mul_ne_zero hA hB
          rw [hQeq, Real.log_div hAmul hCz, Real.log_mul hA hB]
          ring
    calc (∑ z : ↥(A ∪ B) → α,
      shearerMarginal μ (A ∪ B) z * Real.log (shearerQ μ A B z))
      = ∑ z : ↥(A ∪ B) → α, (shearerMarginal μ (A ∪ B) z
        * Real.log (shearerMarginal μ A (shearerResL A B z))
        + shearerMarginal μ (A ∪ B) z * Real.log (shearerMarginal μ B (shearerResR A B z))
        - shearerMarginal μ (A ∪ B) z
          * Real.log (shearerMarginal μ (A ∩ B) (shearerResI A B z))) :=
        Finset.sum_congr rfl (fun z _ => hpoint z)
      _ = (∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z
        * Real.log (shearerMarginal μ A (shearerResL A B z)))
        + (∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z
          * Real.log (shearerMarginal μ B (shearerResR A B z)))
        - (∑ z : ↥(A ∪ B) → α, shearerMarginal μ (A ∪ B) z
          * Real.log (shearerMarginal μ (A ∩ B) (shearerResI A B z))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = _ := by
        rw [reindexA, reindexB, reindexC]
  have hgibbs := gibbs_ineq (shearerMarginal μ (A ∪ B)) (shearerQ μ A B)
    hPnn hQnn hPsum hQsum hsupp
  have hfinal : (-∑ z : ↥(A ∪ B) → α,
    shearerMarginal μ (A ∪ B) z * Real.log (shearerMarginal μ (A ∪ B) z))
    + (-∑ t : ↥(A ∩ B) → α,
      shearerMarginal μ (A ∩ B) t * Real.log (shearerMarginal μ (A ∩ B) t))
    ≤ (-∑ u : ↥A → α, shearerMarginal μ A u * Real.log (shearerMarginal μ A u))
    + (-∑ v : ↥B → α, shearerMarginal μ B v * Real.log (shearerMarginal μ B v)) := by
    have h1 : -(∑ z : ↥(A ∪ B) → α,
      shearerMarginal μ (A ∪ B) z * Real.log (shearerMarginal μ (A ∪ B) z))
      ≤ -(∑ z : ↥(A ∪ B) → α,
        shearerMarginal μ (A ∪ B) z * Real.log (shearerQ μ A B z)) := hgibbs
    have h2 : -(∑ z : ↥(A ∪ B) → α,
      shearerMarginal μ (A ∪ B) z * Real.log (shearerQ μ A B z))
      = (-∑ u : ↥A → α, shearerMarginal μ A u * Real.log (shearerMarginal μ A u))
      + (-∑ v : ↥B → α, shearerMarginal μ B v * Real.log (shearerMarginal μ B v))
      - (-∑ t : ↥(A ∩ B) → α, shearerMarginal μ (A ∩ B) t
        * Real.log (shearerMarginal μ (A ∩ B) t)) := by
      rw [hlogQ]
      ring
    linarith
  unfold shearerMarginalEntropy
  exact hfinal

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerPrefix_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerPrefix_zero (n : ℕ) : shearerPrefix n 0 = ∅ := by
  unfold shearerPrefix
  rw [Finset.filter_false_of_mem]
  intro x _
  omega

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerPrefix_full](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerPrefix_full (n : ℕ) : shearerPrefix n n = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  unfold shearerPrefix
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ i, i.isLt⟩

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerPrefix_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerPrefix_succ (n j : ℕ) (hj : j < n) :
  shearerPrefix n (j + 1) = shearerPrefix n j ∪ {⟨j, hj⟩} := by
  ext i
  simp only [shearerPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro h
    have h2 : i.val < j ∨ i.val = j := by omega
    obtain hlt | heq := h2
    · exact Or.inl hlt
    · exact Or.inr (Fin.ext heq)
  · rintro (hlt | rfl)
    · omega
    · exact Nat.lt_succ_self j

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerMarginalEntropy_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
lemma shearerMarginalEntropy_empty
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
-- given
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1) :
-- imply
  shearerMarginalEntropy μ ∅ = 0 := by
-- proof
  have hsum := shearerMarginal_sum μ hμ_sum ∅
  rw [Fintype.sum_unique] at hsum
  unfold shearerMarginalEntropy
  rw [Fintype.sum_unique, hsum]
  simp

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerMarginalEntropy_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
lemma shearerMarginalEntropy_univ
  [Fintype α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ} :
-- imply
  shearerMarginalEntropy μ Finset.univ = shearerFullEntropy μ := by
-- proof
  let e : (Fin n → α) ≃ (↥(Finset.univ : Finset (Fin n)) → α) :=
    { toFun := fun x s => x s.val
      invFun := fun y i => y ⟨i, Finset.mem_univ i⟩
      left_inv := fun x => rfl
      right_inv := fun y => funext fun s => rfl }
  have hfib : ∀ x : (Fin n → α),
    shearerMarginal μ Finset.univ (e x) = μ x := by
    intro x
    have hcond : ∀ x' : (Fin n → α),
      ((fun s : ↥(Finset.univ : Finset (Fin n)) => x' s.val) = e x) = (x' = x) := by
      intro x'
      apply propext
      constructor
      · intro h
        have h' : e x' = e x := h
        exact e.injective h'
      · intro h
        subst h
        rfl
    unfold shearerMarginal
    simp only [hcond, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hcomp : (∑ y : ↥(Finset.univ : Finset (Fin n)) → α,
    shearerMarginal μ Finset.univ y * Real.log (shearerMarginal μ Finset.univ y))
    = ∑ x : (Fin n → α), shearerMarginal μ Finset.univ (e x)
      * Real.log (shearerMarginal μ Finset.univ (e x)) :=
    (Equiv.sum_comp e _).symm
  unfold shearerMarginalEntropy shearerFullEntropy
  rw [hcomp, neg_inj]
  apply Finset.sum_congr rfl
  intro x _
  rw [hfib x]

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerDimReturns](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerDimReturns {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
  (μ : (Fin n → α) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1)
  (U V : Finset (Fin n)) (i : Fin n) (hVU : V ⊆ U) (hiU : i ∉ U) :
  shearerMarginalEntropy μ (U ∪ {i}) - shearerMarginalEntropy μ U
  ≤ shearerMarginalEntropy μ (V ∪ {i}) - shearerMarginalEntropy μ V := by
  have hU : U ∪ (V ∪ {i}) = U ∪ {i} := by
    ext j
    simp only [Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro (hjU | hjV | rfl)
      · exact Or.inl hjU
      · exact Or.inl (hVU hjV)
      · exact Or.inr rfl
    · rintro (hjU | rfl)
      · exact Or.inl hjU
      · exact Or.inr (Or.inr rfl)
  have hI : U ∩ (V ∪ {i}) = V := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hjU, hjV | rfl⟩
      · exact hjV
      · exact False.elim (hiU hjU)
    · intro hjV
      exact ⟨hVU hjV, Or.inl hjV⟩
  have hsub := shearerMarginalEntropy_submodular μ hμ hμ_sum U (V ∪ {i})
  rw [hU, hI] at hsub
  linarith

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerChainFull](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerChainFull {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
  (μ : (Fin n → α) → ℝ)
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1) :
  shearerMarginalEntropy μ Finset.univ
  = ∑ j ∈ Finset.range n, (shearerMarginalEntropy μ (shearerPrefix n (j + 1))
    - shearerMarginalEntropy μ (shearerPrefix n j)) := by
  have htele : (∑ j ∈ Finset.range n, (shearerMarginalEntropy μ (shearerPrefix n (j + 1))
    - shearerMarginalEntropy μ (shearerPrefix n j)))
    = shearerMarginalEntropy μ (shearerPrefix n n) -
      shearerMarginalEntropy μ (shearerPrefix n 0) :=
    Finset.sum_range_sub (fun j => shearerMarginalEntropy μ (shearerPrefix n j)) n
  rw [htele, shearerPrefix_full n, shearerPrefix_zero n,
    shearerMarginalEntropy_empty μ hμ_sum, sub_zero]

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearerChainMember](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
private lemma shearerChainMember {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
  (μ : (Fin n → α) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1)
  (S : Finset (Fin n)) :
  (∑ i : Fin n, (if i ∈ S then (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
    - shearerMarginalEntropy μ (shearerPrefix n i.val)) else 0))
  ≤ shearerMarginalEntropy μ S := by
  have hteleS : shearerMarginalEntropy μ S
    = ∑ j ∈ Finset.range n, (shearerMarginalEntropy μ (S ∩ shearerPrefix n (j + 1))
      - shearerMarginalEntropy μ (S ∩ shearerPrefix n j)) := by
    have htele : (∑ j ∈ Finset.range n, (shearerMarginalEntropy μ (S ∩ shearerPrefix n (j + 1))
      - shearerMarginalEntropy μ (S ∩ shearerPrefix n j)))
      = shearerMarginalEntropy μ (S ∩ shearerPrefix n n)
        - shearerMarginalEntropy μ (S ∩ shearerPrefix n 0) :=
      Finset.sum_range_sub (fun j => shearerMarginalEntropy μ (S ∩ shearerPrefix n j)) n
    rw [htele, shearerPrefix_full n, shearerPrefix_zero n,
      Finset.inter_univ, Finset.inter_empty,
      shearerMarginalEntropy_empty μ hμ_sum, sub_zero]
  have huniv : (∑ i : Fin n, (shearerMarginalEntropy μ (S ∩ shearerPrefix n (i.val + 1))
    - shearerMarginalEntropy μ (S ∩ shearerPrefix n i.val)))
    = ∑ j ∈ Finset.range n, (shearerMarginalEntropy μ (S ∩ shearerPrefix n (j + 1))
      - shearerMarginalEntropy μ (S ∩ shearerPrefix n j)) :=
    Fin.sum_univ_eq_sum_range (fun j => (shearerMarginalEntropy μ (S ∩ shearerPrefix n (j + 1))
      - shearerMarginalEntropy μ (S ∩ shearerPrefix n j))) n
  rw [hteleS, ← huniv]
  apply Finset.sum_le_sum
  intro i _
  by_cases hiS : i ∈ S
  · simp only [hiS, ↓reduceIte]
    have hTs : shearerPrefix n (i.val + 1) = shearerPrefix n i.val ∪ {i} :=
      shearerPrefix_succ n i.val i.isLt
    have hST : S ∩ shearerPrefix n (i.val + 1) = (S ∩ shearerPrefix n i.val) ∪ {i} := by
      rw [hTs, Finset.inter_union_distrib_left, Finset.inter_singleton_of_mem hiS]
    have hdim := shearerDimReturns μ hμ hμ_sum (shearerPrefix n i.val)
      (S ∩ shearerPrefix n i.val) i Finset.inter_subset_right (by simp [shearerPrefix])
    rwa [hST, hTs]
  · simp only [hiS, ↓reduceIte]
    have hTsub : shearerPrefix n i.val ⊆ shearerPrefix n (i.val + 1) := by
      intro x hx
      simp only [shearerPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      omega
    exact sub_nonneg.mpr (shearerMarginalEntropy_mono μ hμ _ _
      (Finset.inter_subset_inter (Finset.Subset.rfl) hTsub))

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearer_entropy_inequality_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
lemma shearer_entropy_inequality_general
  [Fintype α] [Nonempty α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {C : Finset (Finset (Fin n))}
  {k : ℕ}
-- given
  (hμ_nonneg : ∀ x, 0 ≤ μ x)
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1)
  (hcover : ∀ i : Fin n, k ≤ (C.filter (fun S => i ∈ S)).card) :
-- imply
  (k : ℝ) * shearerFullEntropy μ ≤
    ∑ S ∈ C, shearerMarginalEntropy μ S := by
-- proof
  have hunivEq : shearerMarginalEntropy μ Finset.univ = shearerFullEntropy μ :=
    shearerMarginalEntropy_univ μ
  have hEach : ∀ S ∈ C,
    (∑ i : Fin n, (if i ∈ S then (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
      - shearerMarginalEntropy μ (shearerPrefix n i.val)) else 0))
    ≤ shearerMarginalEntropy μ S :=
    fun S _ => shearerChainMember μ hμ_nonneg hμ_sum S
  calc (k : ℝ) * shearerFullEntropy μ
    = (k : ℝ) * shearerMarginalEntropy μ Finset.univ := by rw [hunivEq]
    _ = (k : ℝ) * ∑ j ∈ Finset.range n, (shearerMarginalEntropy μ (shearerPrefix n (j + 1))
      - shearerMarginalEntropy μ (shearerPrefix n j)) := by
      rw [shearerChainFull μ hμ_sum]
    _ = (k : ℝ) * ∑ i : Fin n, (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
      - shearerMarginalEntropy μ (shearerPrefix n i.val)) := by
      rw [← Fin.sum_univ_eq_sum_range _ n]
    _ = ∑ i : Fin n, (k : ℝ) * (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
      - shearerMarginalEntropy μ (shearerPrefix n i.val)) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ S ∈ C, shearerMarginalEntropy μ S := by
      calc (∑ i : Fin n, (k : ℝ) * (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
        - shearerMarginalEntropy μ (shearerPrefix n i.val)))
        ≤ ∑ i : Fin n, ∑ S ∈ C,
          (if i ∈ S then (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
            - shearerMarginalEntropy μ (shearerPrefix n i.val)) else 0) := by
          apply Finset.sum_le_sum
          intro i _
          have hcard : (∑ S ∈ C,
            (if i ∈ S then (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
              - shearerMarginalEntropy μ (shearerPrefix n i.val)) else 0))
            = ((C.filter (fun S => i ∈ S)).card) •
              (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
                - shearerMarginalEntropy μ (shearerPrefix n i.val)) := by
            rw [← Finset.sum_filter]
            exact Finset.sum_const _
          have hE : 0 ≤ shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
            - shearerMarginalEntropy μ (shearerPrefix n i.val) := by
            have hTsub : shearerPrefix n i.val ⊆ shearerPrefix n (i.val + 1) := by
              intro x hx
              simp only [shearerPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              omega
            exact sub_nonneg.mpr (shearerMarginalEntropy_mono μ hμ_nonneg _ _ hTsub)
          calc (k : ℝ) * (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
            - shearerMarginalEntropy μ (shearerPrefix n i.val))
            ≤ ((C.filter (fun S => i ∈ S)).card : ℝ) *
              (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
                - shearerMarginalEntropy μ (shearerPrefix n i.val)) := by
              apply mul_le_mul_of_nonneg_right _ hE
              exact Nat.cast_le.mpr (hcover i)
            _ = ((C.filter (fun S => i ∈ S)).card) •
              (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
                - shearerMarginalEntropy μ (shearerPrefix n i.val)) := by
              rw [nsmul_eq_mul]
            _ = ∑ S ∈ C, (if i ∈ S then (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
              - shearerMarginalEntropy μ (shearerPrefix n i.val)) else 0) := hcard.symm
        _ = ∑ S ∈ C, ∑ i : Fin n,
          (if i ∈ S then (shearerMarginalEntropy μ (shearerPrefix n (i.val + 1))
            - shearerMarginalEntropy μ (shearerPrefix n i.val)) else 0) :=
          Finset.sum_comm
        _ ≤ ∑ S ∈ C, shearerMarginalEntropy μ S :=
          Finset.sum_le_sum hEach
set_option linter.unusedVariables false in

end MathlibExt.InformationTheory.Shearer

namespace MathlibExt.InformationTheory.Shearer

/--
[shearer_entropy_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean)
-/
@[path]
lemma shearer_entropy_inequality
  [Fintype α] [Nonempty α] [DecidableEq α]
  {n : ℕ}
  {μ : (Fin n → α) → ℝ}
  {C : Finset (Finset (Fin n))}
  {k : ℕ}
-- given
  (hμ_nonneg : ∀ x, 0 ≤ μ x)
  (hμ_sum : ∑ x : (Fin n → α), μ x = 1)
  (hk : 0 < k)
  (hcover : ∀ i : Fin n, k ≤ (C.filter (fun S => i ∈ S)).card) :
-- imply
  (k : ℝ) * shearerFullEntropy μ ≤
    ∑ S ∈ C, shearerMarginalEntropy μ S :=
-- proof
  shearer_entropy_inequality_general μ hμ_nonneg hμ_sum C k hcover

end MathlibExt.InformationTheory.Shearer


-- created on 2026-10-20
-- updated on 2026-10-23
