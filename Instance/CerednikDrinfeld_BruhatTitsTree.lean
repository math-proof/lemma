-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_BruhatTitsTree.lean: instance decls only.
import Class.CerednikDrinfeld_MumfordPeriod
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

set_option autoImplicit false
noncomputable section

open scoped MatrixGroups

namespace CerednikDrinfeld
namespace BruhatTits

open Mumford LT.LatticeTree

namespace _root_.CerednikDrinfeld.Mumford

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W}

instance GraphAction.subgroup (H : Subgroup G) [GraphAction G 𝒯] : GraphAction H 𝒯 :=
  ⟨fun h _ _ hadj => GraphAction.smul_adj (h : G) hadj⟩


end _root_.CerednikDrinfeld.Mumford

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

instance instMulActionGLVertex : MulAction (GL (Fin 2) K) (Vertex R K) where
  smul := Vertex.act
  one_smul := Vertex.act_one
  mul_smul := Vertex.act_mul


instance instMulActionPGLVertex : MulAction (Matrix.ProjGenLinGroup (Fin 2) K) (Vertex R K) :=
  Matrix.ProjGenLinGroup.mulActionOfGL fun c v => scalar_smul_vertex c v


instance instGraphActionGLTree : GraphAction (GL (Fin 2) K) (tree R K) where
  smul_adj g {x y} h := by
    rw [tree_adj_iff] at h ⊢
    refine ⟨fun hxy => h.1 (MulAction.injective g hxy), ?_⟩
    exact h.2.imp (VertRel.gl_smul g) (VertRel.gl_smul g)

instance instGraphActionPGLTree : GraphAction (Matrix.ProjGenLinGroup (Fin 2) K) (tree R K) where
  smul_adj q {x y} h := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g => ?_
    rw [pgl_mk_smul, pgl_mk_smul]
    exact GraphAction.smul_adj g h

end BruhatTits
end CerednikDrinfeld
end
