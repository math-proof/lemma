import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Def.AlgebraicCurve_GluedPic0Pushforward
import Lemma.Definitions.Def_ModularCurve_CharacterLatticePairings
import Def.AlgebraicCurve_GluedPic0SliceOps

set_option autoImplicit false

namespace AlgebraicCurve

open Finset

namespace Pic0Pair

variable {A : Type*} [AddCommGroup A]

theorem blockOp_apply (a b c d : A →+ A) (x y : A) :
    blockOp a b c d (x, y) = (a x + b y, c x + d y) := rfl

theorem blockOp_comp (a b c d a' b' c' d' : A →+ A) :
    (blockOp a b c d).comp (blockOp a' b' c' d') =
      blockOp (a.comp a' + b.comp c') (a.comp b' + b.comp d') (c.comp a' + d.comp c') (c.comp b' + d.comp d') := by
  ext ⟨x, y⟩ <;> simp [blockOp_apply, map_add, add_add_add_comm]

theorem blockOp_diag (a d : A →+ A) : blockOp a 0 0 d = a.prodMap d := by
  ext ⟨x, y⟩ <;> simp [blockOp_apply]

theorem blockOp_one_zero_zero_one : blockOp (AddMonoidHom.id A) 0 0 (AddMonoidHom.id A) = AddMonoidHom.id _ := by
  ext ⟨x, y⟩ <;> simp [blockOp_apply]

end Pic0Pair

namespace NodeData

variable {S S' : Type*} {V V' : Type*}

theorem perm_apply (σ : S ≃ S') (w : S' → V) (s : S) : perm σ w s = w (σ s) := rfl

theorem map_apply (θ : V → V') (w : S → V) (s : S) : map θ w s = θ (w s) := rfl

theorem corr_apply [AddCommGroup V] [Fintype S'] (B : S → S' → ℤ) (w : S' → V) (s : S) :
    corr B w s = ∑ s', B s s' • w s' := rfl

variable [Fintype S] [Fintype S'] {G : Type*} [CommGroup G]

theorem zpowProd_permMapFun_eq (σ : S ≃ S') (a : S → ℤ) (w : S' → Additive G) :
    ModularCurve.CharacterLattice.zpowProd (ModularCurve.CharacterLattice.permMapFun σ a) (fun s' => Additive.toMul (w s')) =
      ModularCurve.CharacterLattice.zpowProd a (fun s => Additive.toMul (perm σ w s)) :=
  ModularCurve.CharacterLattice.zpowProd_permMapFun σ a _

theorem zpowProd_corrMapFun_eq (B : S → S' → ℤ) (a : S → ℤ) (w : S' → Additive G) :
    ModularCurve.CharacterLattice.zpowProd (ModularCurve.CharacterLattice.corrMapFun B a) (fun s' => Additive.toMul (w s')) =
      ModularCurve.CharacterLattice.zpowProd a (fun s => Additive.toMul (corr B w s)) := by
  rw [ModularCurve.CharacterLattice.zpowProd_corrMapFun]
  refine congrArg (ModularCurve.CharacterLattice.zpowProd a) (funext fun s => ?_)
  simp [corr_apply, toMul_sum, toMul_zsmul]

theorem zpowProd_map {G' : Type*} [CommGroup G'] (θ : G →* G') (a : S → ℤ) (w : S → G) :
    ModularCurve.CharacterLattice.zpowProd a (map θ w) = θ (ModularCurve.CharacterLattice.zpowProd a w) := by
  simp [ModularCurve.CharacterLattice.zpowProd_def, map_prod, map_zpow]

end NodeData

namespace GluedPic0

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (S : Finset (Place K F × Place K F)) (g : SemilinearAut K F)

theorem toPic0Pair_glueMap_eq_blockOp (hstab : SemilinearAut.IsNodeStable S g) (ξ : GluedPic0 K F S) :
    toPic0Pair S (glueMap S g hstab ξ) =
      Pic0Pair.blockOp (DistribSMul.toAddMonoidHom (Pic0 K F) g) 0 0
        (DistribSMul.toAddMonoidHom (Pic0 K F) g) (toPic0Pair S ξ) := by
  rw [toPic0Pair_glueMap]
  rcases toPic0Pair S ξ with ⟨x, y⟩
  simp [Pic0Pair.blockOp_apply]

theorem glueMap_nodeUnit_eq (hstab : SemilinearAut.IsNodeStable S g) (w : ↥S → Additive Kˣ) :
    glueMap S g hstab (nodeUnit S w) =
      nodeUnit S (NodeData.map (SemilinearAut.baseAutUnitsHom g)
        (NodeData.perm (SemilinearAut.nodePerm S g hstab).symm w)) :=
  glueMap_nodeUnit S g hstab w

end GluedPic0

end AlgebraicCurve
