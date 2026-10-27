import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.MvFormalGroup_IsShiftBy
import Lemma.Int.P2MUtil

open IsLocalRing MvFormalGroup

/--
[MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add.lean)
-/
@[path]
private lemma main
  [CommRing B] [IsLocalRing B] [CommRing B₁] [Algebra B B₁] [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V] [Module B V] [IsScalarTower B (ResidueField B) V]
  {ι : V →ₗ[B] B}
  {d : ℕ}
  {F : MvFormalGroup d B} [F.IsComm]
  {w w' : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B))}
  {G G' G'' : Deformation (F.map (algebraMap B B₁)) B}
-- given
  (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
  (hι : Function.Injective ι)
  (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁))) :
-- imply
  Deformation.IsShiftBy V ι F 0 G G ∧
      (Deformation.IsShiftBy V ι F w G G' → Deformation.IsShiftBy V ι F w' G' G'' →
        Deformation.IsShiftBy V ι F (w + w') G G'') := by
-- proof
  classical
  refine ⟨?_, ?_⟩
  ·
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro ξ; simp
    · intro l; simp
  · rintro ⟨n, v, z, zl, hzl, hw, hG⟩ ⟨m, v', z', zl', hzl', hw', hG'⟩
    refine ⟨n + m, Fin.append v v', Fin.append z z', Fin.append zl zl', ?_, ?_, ?_⟩
    · intro i l
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using hzl i l
      · simpa only [Fin.append_right] using hzl' j l
    · intro ξ
      rw [LinearMap.add_apply, hw ξ, hw' ξ, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    · intro l
      rw [hG' l, hG l, Fin.sum_univ_add, add_assoc]
      simp only [Fin.append_left, Fin.append_right]


-- created on 2026-10-23
