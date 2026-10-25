import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism.Part2
import Lemma.Nat.IsLiftable_SigmaLinearEquiv
open CoxeterMatrix
open Nat


namespace CoxeterGroup

/--
[sigma_preserves_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicInjective.lean)
-/
@[path]
private lemma sigma_preserves_coord
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {t s₀ : B}
  {v : B → ℝ}
-- given
  (hts : t ≠ s₀) :
-- imply
  sigma M t v s₀ = v s₀ := by
-- proof
  unfold sigma e
  simp [hts]

end CoxeterGroup

namespace CoxeterGroup

/--
[e_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicInjective.lean)
-/
@[path]
private lemma e_self
  [DecidableEq B]
  [Fintype B]
  {s : B} :
-- imply
  e (B := B) s s = (1 : ℝ) := by
-- proof
  unfold e
  exact Pi.single_eq_same s 1

end CoxeterGroup

namespace CoxeterGroup

/--
[sigma_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicInjective.lean)
-/
@[path]
private lemma sigma_injective
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (h : sigma M s = sigma M t) :
-- imply
  s = t := by
-- proof
  by_contra hst
  have h1 : sigma M s (e s) s = -(e s s) := congr_fun (sigma_e_self M s) s
  have h2 : sigma M t (e s) s = e s s := sigma_preserves_coord (M:=M) (t:=t) (s₀:=s) (v:=e s) (Ne.symm hst)
  have h3 : sigma M s (e s) s = sigma M t (e s) s := congr_fun (congr_fun h (e s)) s
  rw [h1, h2] at h3
  rw [e_self] at h3
  linarith
end CoxeterGroup
namespace CoxeterSystem

/--
[simple_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicInjective.lean)
-/
@[path]
private lemma simple_injective
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  Function.Injective cs.simple := by
-- proof
  intro s t hst
  have hrep_s := coxeterRepresentation_simple M cs s
  have hrep_t := coxeterRepresentation_simple M cs t
  have heq : coxeterRepresentation M cs (cs.simple s) =
    coxeterRepresentation M cs (cs.simple t) := by rw [hst]
  rw [hrep_s, hrep_t] at heq
  apply sigma_injective
  ext v u
  have := congr_arg (fun (f : (B → ℝ) ≃ₗ[ℝ] (B → ℝ)) => f v u) heq
  simp only [sigmaLinearEquiv_apply] at this
  exact this

end CoxeterSystem

namespace CoxeterSystem

/--
[coxRep_mul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicInjective.lean)
-/
@[path]
private lemma coxRep_mul_apply
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w₁ w₂ : W}
  {v : B → ℝ} :
-- imply
  (coxeterRepresentation M cs (w₁ * w₂)) v = (coxeterRepresentation M cs w₁) ((coxeterRepresentation M cs w₂) v) := by
-- proof
  have := map_mul (coxeterRepresentation M cs) w₁ w₂
  show (coxeterRepresentation M cs (w₁ * w₂)) v =
    (coxeterRepresentation M cs w₁) ((coxeterRepresentation M cs w₂) v)
  rw [this]
  rfl

end CoxeterSystem

namespace CoxeterSystem

/--
[mem_of_simple_mem_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicInjective.lean)
-/
@[path]
private lemma mem_of_simple_mem_closure
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {S' : Set B}
  {s₀ : B}
-- given
  (hs : cs.simple s₀ ∈ Subgroup.closure (cs.simple '' S')) :
-- imply
  s₀ ∈ S' := by
-- proof
  by_contra hns
  set ρ := coxeterRepresentation M cs
  have closure_preserves : ∀ w, w ∈ Subgroup.closure (cs.simple '' S') →
    ∀ v : B → ℝ, (ρ w) v s₀ = v s₀ := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      intro v
      have hts : t ≠ s₀ := fun h => hns (h ▸ ht)
      change (ρ (cs.simple t)) v s₀ = v s₀
      rw [coxeterRepresentation_simple, sigmaLinearEquiv_apply]
      exact sigma_preserves_coord hts
    | one =>
      intro v
      rw [map_one]
      rfl
    | mul a b _ _ iha ihb =>
      intro v
      rw [coxRep_mul_apply (cs:=cs) (w₁:=a) (w₂:=b) (v:=v)]
      rw [iha, ihb]
    | inv x _ ihx =>
      intro v
      have hcomp : (ρ x) ((ρ x⁻¹) v) = v := by
        have := coxRep_mul_apply (cs:=cs) (w₁:=x) (w₂:=x⁻¹) (v:=v)
        rw [mul_inv_cancel] at this
        rw [← this, map_one]
        rfl
      calc
        _ = (ρ x) ((ρ x⁻¹) v) s₀ := (ihx ((ρ x⁻¹) v)).symm
        _ = v s₀ := by rw [hcomp]
  have repr_preserves := closure_preserves (cs.simple s₀) hs (e s₀)
  have contra : (ρ (cs.simple s₀)) (e s₀) s₀ = -(e s₀ s₀) := by
    change (ρ (cs.simple s₀)) (e s₀) s₀ = _
    rw [coxeterRepresentation_simple, sigmaLinearEquiv_apply]
    exact congr_fun (sigma_e_self M s₀) s₀
  rw [contra] at repr_preserves
  rw [e_self] at repr_preserves
  linarith

end CoxeterSystem

namespace CoxeterSystem

/--
[parabolicSubgroup_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicInjective.lean)
-/
@[path]
private lemma parabolicSubgroup_injective
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {S₁ S₂ : Set B}
-- given
  (h : Subgroup.closure (cs.simple '' S₁) = Subgroup.closure (cs.simple '' S₂)) :
-- imply
  S₁ = S₂ := by
-- proof
  ext s
  constructor
  ·
    intro hs
    exact mem_of_simple_mem_closure (S' := S₂) (s₀ := s)
      (h ▸ Subgroup.subset_closure (Set.mem_image_of_mem cs.simple hs))
  ·
    intro hs
    exact mem_of_simple_mem_closure (S' := S₁) (s₀ := s)
      (h.symm ▸ Subgroup.subset_closure (Set.mem_image_of_mem cs.simple hs))

end CoxeterSystem


-- created on 2026-10-24
