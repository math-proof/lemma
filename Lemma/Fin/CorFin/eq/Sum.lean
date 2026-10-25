import Mathlib
import sympy.Basic
import Lemma.GroupCohomology.Corestriction2
open CategoryTheory groupCohomology
set_option autoImplicit false


variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G}

variable [H.FiniteIndex] (A : Rep.{0} k G) (τ : groupCohomology.Cores.Transversal H)

attribute [local instance] fintypeQuot

noncomputable def CorFin (n : ℕ) (u : (Fin n → H) → A) : (Fin n → G) → A := fun g =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q)
    (u (fun i => (τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g (Fin.castSucc i)))⁻¹
                   * τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g i.succ)))


/--
[corFin_apply]
-/
@[path]
private lemma main
-- given
  (n : ℕ) (u : (Fin n → H) → A) (g : Fin n → G) :
-- imply
  CorFin A τ n u g =
    ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (fun i => (τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g (Fin.castSucc i)))⁻¹ * τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g i.succ))) := by
-- proof
  rfl


-- created on 2026-10-24

