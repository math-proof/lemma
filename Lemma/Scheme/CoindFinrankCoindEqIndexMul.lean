import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul.lean)
-/
@[path]
private lemma main
  {k G : Type u} [Field k] [Group G]
  (S : Subgroup G) [S.FiniteIndex]
  (N : Rep k S) [FiniteDimensional k N] :
  -- imply
  FiniteDimensional k (Rep.coind S.subtype N) ∧ Module.finrank k (Rep.coind S.subtype N) = S.index * Module.finrank k N := by
  -- proof
  classical
  let Q := Quotient (QuotientGroup.rightRel S)
  let _ : Finite Q := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  let _ : Fintype Q := Fintype.ofFinite Q
  let rep : G → G := fun g => (Quotient.mk (QuotientGroup.rightRel S) g).out
  have rep_spec : ∀ g : G, g * (rep g)⁻¹ ∈ S := fun g => QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel S) g)
  have rep_mul : ∀ (s : S) (g : G), rep ((s : G) * g) = rep g := fun s g => by
    show (Quotient.mk _ ((s : G) * g)).out = (Quotient.mk _ g).out
    congr 1
    apply Quotient.sound
    show @Setoid.r _ (QuotientGroup.rightRel S) ((s : G) * g) g
    rw [QuotientGroup.rightRel_apply]
    simp
  have key : ∀ (a : G) (ha : a ∈ S) (v : N), a = 1 → N.ρ ⟨a, ha⟩ v = v := by
    rintro a ha v rfl
    apply congrFun (congrArg DFunLike.coe (map_one N.ρ)) v
  let invFun : (Q → N) → Rep.coind S.subtype N := fun F => ⟨fun g => N.ρ ⟨g * (rep g)⁻¹, rep_spec g⟩ (F (Quotient.mk _ g)), fun s h => by
    simp only [Subgroup.coe_subtype]
    have hrel : @Setoid.r _ (QuotientGroup.rightRel S) ((s : G) * h) h := by
      rw [QuotientGroup.rightRel_apply]
      simp
    have hq : (Quotient.mk (QuotientGroup.rightRel S) ((s : G) * h)) = Quotient.mk _ h := Quotient.sound hrel
    rw [← Module.End.mul_apply, ← map_mul]
    have hmem : (s : G) * h * (rep ((s : G) * h))⁻¹ ∈ S := rep_spec _
    have this : (⟨(s : G) * h * (rep ((s : G) * h))⁻¹, hmem⟩ : S) = s * ⟨h * (rep h)⁻¹, rep_spec h⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, rep_mul, mul_assoc]
    rw [show (⟨(s : G) * h * (rep ((s : G) * h))⁻¹, rep_spec _⟩ : S) = s * ⟨h * (rep h)⁻¹, rep_spec h⟩ from this, hq]⟩
  have left_inv (f : Rep.coind S.subtype N) : invFun (fun q => (f : G → N) q.out) = f := by
    apply Subtype.ext
    funext g
    show N.ρ ⟨g * (rep g)⁻¹, rep_spec g⟩ ((f : G → N) (Quotient.mk (QuotientGroup.rightRel S) g).out) = (f : G → N) g
    have := f.2 ⟨g * (rep g)⁻¹, rep_spec g⟩ (rep g)
    rw [← this]
    show (f : G → N) (g * (rep g)⁻¹ * rep g) = (f : G → N) g
    rw [inv_mul_cancel_right]
  have right_inv (F : Q → N) : (fun q => (invFun F : G → N) q.out) = F := by
    funext q
    show N.ρ ⟨q.out * (rep q.out)⁻¹, rep_spec q.out⟩ (F (Quotient.mk _ q.out)) = F q
    have hout : Quotient.mk (QuotientGroup.rightRel S) q.out = q := Quotient.out_eq q
    rw [hout]
    have h1 : q.out * ((Quotient.mk (QuotientGroup.rightRel S) q.out).out)⁻¹ = 1 := by
      show q.out * ((Quotient.mk (QuotientGroup.rightRel S) q.out).out)⁻¹ = 1
      rw [hout, mul_inv_cancel]
    refine key _ _ _ h1
  let e : Rep.coind S.subtype N ≃ₗ[k] (Q → N) := LinearEquiv.mk (⟨⟨fun f q => (f : G → N) q.out, fun _ _ => rfl⟩, fun _ _ => rfl⟩ : Rep.coind S.subtype N →ₗ[k] (Q → N)) invFun left_inv right_inv
  let _ : FiniteDimensional k (Rep.coind S.subtype N) := LinearEquiv.finiteDimensional e.symm
  refine ⟨inferInstance, ?_⟩
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, Subgroup.index, ← Nat.card_eq_fintype_card, Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]


-- created on 2026-10-20
