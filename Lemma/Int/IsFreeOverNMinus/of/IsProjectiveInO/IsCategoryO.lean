import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.ExtO.Part2


/--
[projective_in_O_is_nminus_retract_of_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ExtO.lean)
-/
@[path]
private lemma projective_in_O_is_nminus_retract_of_free
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {P : Type uCatO}
  [AddCommGroup P]
  [Module R P]
  [LieRingModule 𝔤 P]
  [LieModule R 𝔤 P]
-- given
  (_hPO : IsCategoryO Δ rd P)
  (_hPproj : IsProjectiveInO rd P _hPO) :
-- imply
  letI _instP := instModuleUEASubalg Δ.𝔫_neg P ∃ (Q : Type uCatO) (_ : AddCommGroup Q) (_ : Module R Q) (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q), letI _instQ := instModuleUEASubalg Δ.𝔫_neg Q Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) Q ∧ ∃ (ι : P →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] Q) (s : Q →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] P), s.comp ι = LinearMap.id := by
-- proof
  letI : Module (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) P := instModuleUEASubalg Δ.𝔫_neg P
  haveI hFree : Module.Free (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) P :=
    projective_in_O_is_free_U_nminus (wg := wg) _hPO _hPproj
  exact ⟨P, inferInstance, inferInstance, inferInstance, inferInstance,
    hFree, LinearMap.id, LinearMap.id, LinearMap.id_comp _⟩

/--
[projective_in_O_is_free_nminus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ExtO.lean)
-/
@[path]
private lemma projective_in_O_is_free_nminus
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {P : Type uCatO}
  [AddCommGroup P]
  [Module R P]
  [LieRingModule 𝔤 P]
  [LieModule R 𝔤 P]
-- given
  (hPO : IsCategoryO Δ rd P)
  (_hPproj : IsProjectiveInO rd P hPO) :
-- imply
  IsFreeOverNMinus (Δ := Δ) P := by
-- proof
  unfold IsFreeOverNMinus
  letI := instModuleUEASubalg Δ.𝔫_neg P
  exact projective_in_O_is_free_U_nminus (wg := wg) hPO _hPproj

/--
[UEA_induction_on](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ExtO.lean)
-/
@[path]
private lemma UEA_induction_on_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing L]
  [LieAlgebra R L]
  {C : UniversalEnvelopingAlgebra R L → Prop}
  {u : UniversalEnvelopingAlgebra R L}
-- given
  (h_alg : ∀ r : R, C (algebraMap R _ r))
  (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b)) :
-- imply
  C u := by
-- proof
  apply UEA_induction_on R 𝔤 u h_alg h_ι h_mul h_add

/--
[lieModuleHom_ueaSubalg_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ExtO.lean)
-/
@[path]
private lemma lieModuleHom_ueaSubalg_compat_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {f : M →ₗ⁅R, 𝔤⁆ N}
  {u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg}
  {m : M} :
-- imply
  f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
-- proof
  apply lieModuleHom_ueaSubalg_compat R 𝔤 f u m


-- created on 2026-10-23
-- updated on 2026-10-26
