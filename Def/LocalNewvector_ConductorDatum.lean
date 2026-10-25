import Def.LocalNewvector_CongruenceSubgroupK1
import Instance.RepTheory_GL2CongruenceSubgroup
import Def.LocalLanglands_LocalHeckeInstance

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

def fixedSubmodule {G : Type*} [Group G] (U : Subgroup G) (V : Type*) [AddCommGroup V]
    [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] : Submodule ℂ V where
  carrier := {v | ∀ g ∈ U, g • v = v}
  add_mem' := by
    intro v w hv hw g hg
    rw [smul_add, hv g hg, hw g hg]
  zero_mem' := by
    intro g _
    exact smul_zero g
  smul_mem' := by
    intro c v hv g hg
    rw [smul_comm, hv g hg]


section Padic

variable (p : ℕ) [Fact p.Prime]


def centralGL : ℚ_[p]ˣ →* GL (Fin 2) ℚ_[p] :=
  Units.map (algebraMap ℚ_[p] (Matrix (Fin 2) (Fin 2) ℚ_[p])).toMonoidHom

def IsCentralCharacterRep (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] (ω : ℚ_[p]ˣ →* ℂˣ) : Prop :=
  ∀ (u : ℚ_[p]ˣ) (v : V), centralGL p u • v = (ω u : ℂ) • v


def HasNewvectorConductor (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    (c : ℕ) : Prop :=
  fixedSubmodule (padicK1 p c) V ≠ ⊥ ∧ ∀ m < c, fixedSubmodule (padicK1 p m) V = ⊥


def IsIrreducibleGLRep (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] : Prop :=
  (∃ v : V, v ≠ 0) ∧
  ∀ W : Submodule ℂ V,
    (∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤

def HasFiniteLevelFixed (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V] : Prop :=
  ∀ n : ℕ, Module.Finite ℂ (fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup p n) V)

end Padic

end LocalNewvector

end
