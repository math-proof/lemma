import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Representation_exists_ne_zero_forall_apply_eq_of_isPGroup](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Representation_exists_ne_zero_forall_apply_eq_of_isPGroup.lean)
-/
@[path]
private lemma main
  [Field k]
  {p : ℕ} [Fact p.Prime] [CharP k p]
  [Group G] [Finite G] (hG : IsPGroup p G)
  [AddCommGroup V] [Module k V] (ρ : Representation k G V) {v : V} (hv : v ≠ 0) :
    -- imply
    ∃ w : V, w ≠ 0 ∧ ∀ g : G, ρ g w = w := by
    -- proof
  classical
  let modp : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
  have hsmul : ∀ (c : ZMod p) (x : V), c • x = ((ZMod.castHom (dvd_refl p) k c : k)) • x := fun _ _ => rfl
  set S : Set V := Set.range fun g : G => ρ g v with hS
  set W : Submodule (ZMod p) V := Submodule.span (ZMod p) S with hW
  have hWstab : ∀ (g : G) {x : V}, x ∈ W → ρ g x ∈ W := by
    intro g x hx
    induction hx using Submodule.span_induction
    ·
      rename_i y hy
      obtain ⟨h, rfl⟩ := hy
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
    ·
      rw [map_zero]
      apply W.zero_mem
    ·
      rename_i y z _ _ hy hz
      rw [map_add]
      apply W.add_mem hy hz
    ·
      rename_i c y _ hy
      rw [hsmul, map_smul, ← hsmul]
      apply W.smul_mem c hy
  let _ : Module.Finite (ZMod p) W := Module.Finite.span_of_finite (ZMod p) (Set.finite_range _)
  let _ : Finite W := Module.finite_of_finite (ZMod p)
  let act : MulAction G W :=
    { smul := fun g w => ⟨ρ g w, hWstab g w.2⟩
      one_smul := fun w => Subtype.ext (by show ρ 1 (w : V) = w; rw [map_one]; rfl)
      mul_smul := fun g h w => Subtype.ext (by show ρ (g * h) (w : V) = ρ g (ρ h w); rw [map_mul]; rfl) }
  have hact : ∀ (g : G) (w : W), ((g • w : W) : V) = ρ g w := fun _ _ => rfl
  have hmod := hG.card_modEq_card_fixedPoints W
  have hvW : (⟨v, Submodule.subset_span ⟨1, by simp⟩⟩ : W) ≠ 0 := fun h => hv (congrArg Subtype.val h)
  have hpW : p ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := W), Nat.card_zmod]
    refine dvd_pow_self p (Module.finrank_pos_iff.mpr ⟨⟨_, 0, hvW⟩⟩).ne'
  have hpF : p ∣ Nat.card (MulAction.fixedPoints G W) := by
    apply Nat.dvd_of_mod_eq_zero
    have h1 : Nat.card W % p = 0 := Nat.mod_eq_zero_of_dvd hpW
    have h2 : Nat.card W % p = Nat.card (MulAction.fixedPoints G W) % p := hmod
    omega
  have h0 : (0 : W) ∈ MulAction.fixedPoints G W := fun g => Subtype.ext (by rw [hact]; apply map_zero _)
  let _ : Finite (MulAction.fixedPoints G W) := inferInstance
  have hcard : 1 < Nat.card (MulAction.fixedPoints G W) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints G W) := Nat.card_pos_iff.mpr ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
    refine lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hpF)
  rw [Finite.one_lt_card_iff_nontrivial] at hcard
  obtain ⟨⟨y, hy⟩, hy0⟩ := exists_ne (⟨0, h0⟩ : MulAction.fixedPoints G W)
  refine ⟨(y : V), fun h => hy0 (Subtype.ext (Subtype.ext h)), fun g => ?_⟩
  have := hy g
  rw [Subtype.ext_iff, hact] at this
  apply this


-- created on 2026-10-20
