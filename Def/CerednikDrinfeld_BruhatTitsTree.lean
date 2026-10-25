import Lemma.LatticeTreeOrbital.Main
import Class.CerednikDrinfeld_MumfordPeriod
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

set_option autoImplicit false
noncomputable section

open scoped MatrixGroups

namespace CerednikDrinfeld
namespace BruhatTits

open Mumford LT.LatticeTree


variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]


variable (R K) in

def vertPermHom : GL (Fin 2) K →* Equiv.Perm (Vertex R K) := MulAction.toPermHom (GL (Fin 2) K) (Vertex R K)


variable [IsFractionRing R K]


variable (R K) in

def VertRel (x y : Vertex R K) : Prop :=
  ∃ (L L' : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) (hL' : IsFullLattice L'),
    Vertex.mk R K L hL = x ∧ Vertex.mk R K L' hL' = y ∧ AdjacentLattice L L'

variable (R K) in

def tree : SimpleGraph (Vertex R K) := SimpleGraph.fromRel (VertRel R K)

end BruhatTits

end CerednikDrinfeld

end
