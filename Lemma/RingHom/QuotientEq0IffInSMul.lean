import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[MonoidAlgebra_quotient_mk_eq_zero_iff_mem_map_augmentation_smul_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MonoidAlgebra_quotient_mk_eq_zero_iff_mem_map_augmentation_smul_top.lean)
-/
@[path]
private lemma main
  {𝒪 A G Mn : Type} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] [CommGroup G] [Fintype G] [AddCommGroup Mn] [Module A Mn] [Module (MonoidAlgebra 𝒪 G) Mn] [Module 𝒪 Mn] [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 G) Mn]
  (ι : AlgHom 𝒪 (MonoidAlgebra 𝒪 G) A)
  (x : Mn)
  -- given
  (hι : ∀ (c : MonoidAlgebra 𝒪 G) (x : Mn), c • x = ι c • x) :
  -- imply
  (Submodule.Quotient.mk x : Mn ⧸ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)) • (⊤ : Submodule (MonoidAlgebra 𝒪 G) Mn))) = 0 ↔ x ∈ (Ideal.map ι (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)))) • (⊤ : Submodule A Mn) := by
  -- proof
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  ·
    intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    ·
      intro c hc m _
      rw [hι]
      apply Submodule.smul_mem_smul (Ideal.mem_map_of_mem ι hc) Submodule.mem_top
    ·
      intro a b ha hb
      apply Submodule.add_mem _ ha hb
  ·
    intro hx
    have key : ∀ a ∈ Ideal.map ι (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G))), ∀ m : Mn, a • m ∈ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)) • (⊤ : Submodule (MonoidAlgebra 𝒪 G) Mn)) := by
      intro a ha
      rw [Ideal.map] at ha
      refine Submodule.span_induction (p := fun a _ => ∀ m : Mn, a • m ∈ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)) • (⊤ : Submodule (MonoidAlgebra 𝒪 G) Mn))) ?_ ?_ ?_ ?_ ha
      ·
        rintro _ ⟨c, hc, rfl⟩ m
        rw [← hι]
        apply Submodule.smul_mem_smul hc Submodule.mem_top
      ·
        intro m
        rw [zero_smul]
        apply Submodule.zero_mem _
      ·
        intro a b _ _ ha hb m
        rw [add_smul]
        apply Submodule.add_mem _ (ha m) (hb m)
      ·
        intro s b _ hb m
        rw [smul_eq_mul, mul_comm, mul_smul]
        apply hb (s • m)
    refine Submodule.smul_induction_on hx ?_ ?_
    ·
      intro a ha m _
      apply key a ha m
    ·
      intro a b ha hb
      apply Submodule.add_mem _ ha hb


-- created on 2026-10-20
