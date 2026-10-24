import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.PBWLieSubmodBridge


/--
[UniversalEnvelopingAlgebra.algHom_ext'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PBWLieSubmodBridge.lean)
-/
@[path]
private lemma UniversalEnvelopingAlgebra.algHom_ext'
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [Ring A]
  [Algebra R A]
  {g₁ g₂ : UniversalEnvelopingAlgebra R L →ₐ[R] A}
-- given
  (h : ∀ x : L, g₁ (UniversalEnvelopingAlgebra.ι R x) = g₂ (UniversalEnvelopingAlgebra.ι R x)) :
-- imply
  g₁ = g₂ := by
-- proof
  have h1 := (UniversalEnvelopingAlgebra.lift R).apply_symm_apply g₁
  have h2 := (UniversalEnvelopingAlgebra.lift R).apply_symm_apply g₂
  rw [← h1, ← h2]; congr 1; ext x
  have := h x; rw [← h1, ← h2] at this; simpa using this
section LieSubmoduleBridge
variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]
variable [Module (UniversalEnvelopingAlgebra R L) M]
variable [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]

/--
[LieSubmodule.preservingSubalgebra_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PBWLieSubmodBridge.lean)
-/
@[path]
private lemma LieSubmodule.preservingSubalgebra_eq_top
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule L M]
  [LieModule R L M]
  [Module (UniversalEnvelopingAlgebra R L) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
  {N : LieSubmodule R L M}
-- given
  (hcompat : ∀ (x : L) (m : M), ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
-- imply
  N.preservingSubalgebra = ⊤ := by
-- proof
  rw [eq_top_iff]; intro u _
  let S := N.preservingSubalgebra
  let ιS : L →ₗ⁅R⁆ S :=
    { toFun := fun x => ⟨UniversalEnvelopingAlgebra.ι R x, fun m hm => by
      rw [← hcompat]; exact N.lie_mem hm⟩
      map_add' := fun x y => by ext; simp [map_add]
      map_smul' := fun r x => by ext; simp [map_smul]
      map_lie' := fun {x y} => by
        ext; simp [LieRing.of_associative_ring_bracket] }
  let Ψ := UniversalEnvelopingAlgebra.lift R ιS
  have hΨ : S.val.comp Ψ = AlgHom.id R _ :=
    UniversalEnvelopingAlgebra.algHom_ext' (fun x => by
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, Subalgebra.coe_val, Ψ,
        UniversalEnvelopingAlgebra.lift_ι_apply, ιS]
      rfl)
  have : S.val (Ψ u) = u := AlgHom.congr_fun hΨ u
  rw [← this]; exact (Ψ u).2

/--
[LieSubmodule.mem_toUEASubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PBWLieSubmodBridge.lean)
-/
@[path]
private lemma LieSubmodule.mem_toUEASubmodule
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule L M]
  [LieModule R L M]
  [Module (UniversalEnvelopingAlgebra R L) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
  {N : LieSubmodule R L M}
  {m : M}
-- given
  (hcompat : ∀ (x : L) (m : M), ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
-- imply
  m ∈ N.toUEASubmodule hcompat ↔ m ∈ N :=
-- proof
  Iff.rfl

/--
[LieSubmodule.toUEASubmodule_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PBWLieSubmodBridge.lean)
-/
@[path]
private lemma LieSubmodule.toUEASubmodule_bot
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule L M]
  [LieModule R L M]
  [Module (UniversalEnvelopingAlgebra R L) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
-- given
  (hcompat : ∀ (x : L) (m : M), ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
-- imply
  (⊥ : LieSubmodule R L M).toUEASubmodule hcompat = ⊥ := by
-- proof
  ext m
  simp only [LieSubmodule.mem_toUEASubmodule, LieSubmodule.mem_bot, Submodule.mem_bot]

/--
[LieSubmodule.toUEASubmodule_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PBWLieSubmodBridge.lean)
-/
@[path]
private lemma LieSubmodule.toUEASubmodule_top
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule L M]
  [LieModule R L M]
  [Module (UniversalEnvelopingAlgebra R L) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
-- given
  (hcompat : ∀ (x : L) (m : M), ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
-- imply
  (⊤ : LieSubmodule R L M).toUEASubmodule hcompat = ⊤ := by
-- proof
  ext m
  simp only [LieSubmodule.mem_toUEASubmodule, LieSubmodule.mem_top, Submodule.mem_top]

/--
[LieSubmodule.toUEASubmodule_ofUEASubmodule'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PBWLieSubmodBridge.lean)
-/
@[path]
private lemma LieSubmodule.toUEASubmodule_ofUEASubmodule'
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule L M]
  [LieModule R L M]
  [Module (UniversalEnvelopingAlgebra R L) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
  {N : Submodule (UniversalEnvelopingAlgebra R L) M}
-- given
  (hcompat : ∀ (x : L) (m : M), ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m) :
-- imply
  (LieSubmodule.ofUEASubmodule' hcompat N).toUEASubmodule hcompat = N := by
-- proof
  ext m; rfl
end LieSubmoduleBridge


-- created on 2026-10-23
-- updated on 2026-10-24
