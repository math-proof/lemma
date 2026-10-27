import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[idealToSubmoduleMap_order_reflecting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TranslationFunctors.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type v} [Ring A] [Algebra R A]
  {M : Type w} [AddCommGroup M] [Module R M]
  {act : A →ₐ[R] Module.End R M}
  {v : M}
  {I J : TwoSidedIdeal A}
-- given
  (hinj : Function.Injective fun u => act u v)
  (hsurj : Function.Surjective fun u => act u v)
  (hle :
    Submodule.span R {m : M | ∃ j ∈ I, ∃ x : M, m = act j x} ≤
      Submodule.span R {m : M | ∃ j ∈ J, ∃ x : M, m = act j x}) :
-- imply
  I ≤ J := by
-- proof
  intro a ha
  have key :
    act a v ∈ Submodule.span R {m : M | ∃ j ∈ J, ∃ x : M, m = act j x} :=
    hle (Submodule.subset_span ⟨a, ha, v, rfl⟩)
  let ev : A →ₗ[R] M :=
    { toFun := fun u => act u v
      map_add' := fun x y => by
        simp [map_add, LinearMap.add_apply]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        show act (r • x) v = r • act x v
        rw [Algebra.smul_def, map_mul]
        simp [AlgHom.commutes] }
  let JR : Submodule R A :=
    { carrier := (J : Set A)
      add_mem' := fun {x y} hx hy => J.add_mem hx hy
      zero_mem' := J.zero_mem
      smul_mem' := fun r x hx => by
        rw [Algebra.smul_def]
        apply J.mul_mem_left
        apply hx }
  have gen_sub :
    {m : M | ∃ j ∈ J, ∃ x : M, m = act j x} ⊆ (Submodule.map ev JR : Set M) := by
    intro m ⟨j', hj', x, hx⟩
    obtain ⟨u, hu⟩ := hsurj x
    refine ⟨j' * u, ?_, ?_⟩
    ·
      apply J.mul_mem_right
      apply hj'
    ·
      change act (j' * u) v = m
      rw [hx, ← hu, map_mul]
      rfl
  have key2 : act a v ∈ Submodule.map ev JR :=
    (Submodule.span_le.mpr gen_sub) key
  rw [Submodule.mem_map] at key2
  obtain ⟨b, hbJ, hbv⟩ := key2
  have hbv' : act b v = act a v := hbv
  have hab : a = b := hinj hbv'.symm
  rw [hab]
  apply hbJ


-- created on 2026-10-23
-- updated on 2026-10-26
