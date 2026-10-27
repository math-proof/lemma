import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
open CategoryTheory


/--
[thm_1_22_11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaHopfReconstruction.lean)
-/
@[path]
lemma thm_1_22_11
  {k : Type w}
  [Field k] :
-- imply
  (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C] [Linear k C] [RigidCategory C] (F : C ⥤ ModuleCat.{w} k) (hFaithful : F.Faithful) (hMono : F.PreservesMonomorphisms) (hEpi : F.PreservesEpimorphisms) (hMonoidal : F.Monoidal), Nonempty (FiniteTannakaHopfData k C)) ∧ (∀ (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H], Nonempty (HopfAlgebraRepData k H)) ∧ (∀ (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H] (repData : HopfAlgebraRepData k H) [instLinear : Linear k repData.RepH] (reconData : FiniteTannakaHopfData (C := repData.RepH) k), Nonempty (BialgebraEquiv k reconData.H H)) := by
-- proof
  exact ⟨fun C _ _ _ _ _ F hF hM hE hMon =>
    ⟨tannaka_hopf_reconstruction k C F hF hM hE hMon⟩,
    fun H _ _ _ _ => ⟨tannaka_hopf_inverse k H⟩,
    fun H _ _ _ _ repData _ reconData =>
      tannaka_hopf_roundtrip_algebra k H repData reconData⟩


-- created on 2026-10-23
