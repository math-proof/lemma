import Mathlib
import sympy.Basic


/--
[MonoidHom_exists_subfield_units_coe_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MonoidHom_exists_subfield_units_coe_eq.lean)
-/
@[path]
private lemma main
  [Group G] [Field L]
  {K : Subfield L}
  {F : G →* G →* Lˣ}
-- given
  (hF : ∀ α β : G, ((F α β : Lˣ) : L) ∈ K) :
-- imply
  ∃ F' : G →* G →* (↥K)ˣ, ∀ α β : G, (((F' α β : (↥K)ˣ) : ↥K) : L) = F α β := by
-- proof
  have hinv : ∀ α β : G, ((F α β : Lˣ) : L)⁻¹ ∈ K := fun α β => K.inv_mem (hF α β)
  let u : G → G → (↥K)ˣ := fun α β =>
    ⟨⟨(F α β : L), hF α β⟩, ⟨((F α β : Lˣ) : L)⁻¹, hinv α β⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩
  have hu : ∀ α β, (((u α β : (↥K)ˣ) : ↥K) : L) = F α β := fun _ _ => rfl
  refine ⟨{ toFun := fun α => { toFun := u α, map_one' := ?_, map_mul' := ?_ }, map_one' := ?_, map_mul' := ?_ }, hu⟩
  · ext; simp [u]
  · intro β₁ β₂; ext; simp [u, Units.val_mul]
  · ext β; simp [u]
  · intro α₁ α₂; ext β; simp [u, Units.val_mul]


-- created on 2026-10-05
