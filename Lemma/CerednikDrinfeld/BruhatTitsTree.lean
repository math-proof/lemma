import Lemma.LatticeTreeOrbital.Main
import Class.CerednikDrinfeld_MumfordPeriod
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Def.CerednikDrinfeld_BruhatTitsTree

set_option autoImplicit false
noncomputable section

open scoped MatrixGroups

namespace CerednikDrinfeld
namespace BruhatTits

open Mumford LT.LatticeTree

namespace _root_.CerednikDrinfeld.Mumford

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W}


theorem GraphAction.of_compHom {G' : Type} [Group G'] (φ : G' →* G) [GraphAction G 𝒯] :
    @GraphAction G' _ W (MulAction.compHom W φ) 𝒯 :=
  @GraphAction.mk G' _ W (MulAction.compHom W φ) 𝒯 fun g _ _ hadj => GraphAction.smul_adj (φ g) hadj

end _root_.CerednikDrinfeld.Mumford

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]


theorem gl_smul_def (g : GL (Fin 2) K) (v : Vertex R K) : g • v = Vertex.act g v := rfl

@[simp] theorem gl_smul_mk (g : GL (Fin 2) K) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    g • Vertex.mk R K L hL = Vertex.mk R K (latticeMap g L) (hL.map g) := rfl


@[simp] theorem vertPermHom_apply (g : GL (Fin 2) K) (x : Vertex R K) : vertPermHom R K g x = g • x := rfl

theorem scalar_eq_scalarGL (c : Kˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) c = scalarGL c := by
  ext i j
  simp [Matrix.GeneralLinearGroup.coe_scalar, scalarGL_coe, Matrix.one_apply, Matrix.diagonal_apply]

theorem scalar_smul_vertex (c : Kˣ) (v : Vertex R K) : Matrix.GeneralLinearGroup.scalar (Fin 2) c • v = v := by
  rw [scalar_eq_scalarGL]
  exact isFixedVertex_scalarGL c v

theorem scalar_mem_ker_vertPermHom (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ (vertPermHom R K).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  simp [scalar_smul_vertex]


@[simp] theorem pgl_mk_smul (g : GL (Fin 2) K) (v : Vertex R K) : Matrix.ProjGenLinGroup.mk g • v = g • v := rfl

variable [IsFractionRing R K]

theorem adjacentLattice_latticeMap (g : GL (Fin 2) K) {L L' : Submodule R (Fin 2 → K)}
    (h : AdjacentLattice L L') : AdjacentLattice (latticeMap g L) (latticeMap g L') := by
  obtain ⟨ϖ, hϖ, h₁, h₂⟩ := h
  refine ⟨ϖ, hϖ, ?_, (latticeMap_lt_latticeMap_iff g).2 h₂⟩
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]
  exact (latticeMap_lt_latticeMap_iff g).2 h₁


theorem tree_adj_iff (x y : Vertex R K) :
    (tree R K).Adj x y ↔ x ≠ y ∧ (VertRel R K x y ∨ VertRel R K y x) :=
  SimpleGraph.fromRel_adj _ _ _

theorem VertRel.gl_smul (g : GL (Fin 2) K) {x y : Vertex R K} (h : VertRel R K x y) :
    VertRel R K (g • x) (g • y) := by
  obtain ⟨L, L', hL, hL', rfl, rfl, hLL'⟩ := h
  exact ⟨latticeMap g L, latticeMap g L', hL.map g, hL'.map g, rfl, rfl, adjacentLattice_latticeMap g hLL'⟩

end BruhatTits

end CerednikDrinfeld

end
