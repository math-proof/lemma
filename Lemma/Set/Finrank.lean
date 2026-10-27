import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[HopfOrder_finrank_eq_finrank](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfOrder_finrank_eq_finrank.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type u} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
  (S : Subalgebra R A)
  (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤) :
  -- imply
  Module.finrank R ↥S = Module.finrank K A := by
  -- proof
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let hRA : Module.IsTorsionFree R A :=
    Module.IsTorsionFree.comap (algebraMap R K)
      (fun r hr => IsRegular.of_ne_zero (fun h0 => hr.ne_zero (hinj (by rw [h0, map_zero]))))
      (fun r m => algebraMap_smul K r m)
  let hRS : Module.IsTorsionFree R ↥S :=
    Function.Injective.moduleIsTorsionFree (fun x : ↥S => (x : A)) Subtype.val_injective (fun _ _ => rfl)
  let _ : Module.Finite R ↥S := hfin
  let _ : Module.Free R ↥S := inferInstance
  let b := Module.Free.chooseBasis R ↥S
  let v : Module.Free.ChooseBasisIndex R ↥S → A := fun i => (b i : A)
  have hvR : LinearIndependent R v :=
    b.linearIndependent.map' S.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hvK : LinearIndependent K v := (LinearIndependent.iff_fractionRing R K).mp hvR
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    have hxR : x ∈ Submodule.span R (Set.range v) := by
      have hmem : (⟨x, hx⟩ : ↥S) ∈ Submodule.span R (Set.range b) := by
        rw [b.span_eq]
        apply Submodule.mem_top
      have himg := Submodule.mem_map_of_mem (f := S.val.toLinearMap) hmem
      rw [Submodule.map_span, ← Set.range_comp] at himg
      apply himg
    refine Submodule.span_le_restrictScalars R K (Set.range v) hxR
  let bK : Module.Basis (Module.Free.ChooseBasisIndex R ↥S) K A := Module.Basis.mk hvK hsp
  rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis bK]


-- created on 2026-10-20
