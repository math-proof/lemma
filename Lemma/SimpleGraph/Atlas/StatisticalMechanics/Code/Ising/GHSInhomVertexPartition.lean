import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
open Finset Classical StatMech StatMech.Ising


/--
[ghsiGhostCoupling_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsiGhostCoupling_some_some_eq
  [Fintype V]
  [DecidableEq V]
  {K : Sym2 V → ℝ}
  {x y : V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiGhostCoupling K hf s(some x, some y) = 2 * K s(x, y) := by
-- proof
  apply StatMech.Ising.ghsiGhostCoupling_some_some K hf x y

/--
[ghsiGhostCoupling_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsiGhostCoupling_some_none_eq
  [Fintype V]
  [DecidableEq V]
  {K : Sym2 V → ℝ}
  {x : V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiGhostCoupling K hf s(some x, none) = 2 * hf x := by
-- proof
  apply StatMech.Ising.ghsiGhostCoupling_some_none K hf x

/--
[ghsi_fieldSet_couplingSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsi_fieldSet_couplingSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {A : Finset V}
  {s : ConfigSpace (Option V)}
-- given
  (hf : V → ℝ) :
-- imply
  (∑ e ∈ ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A), ghsiGhostCoupling K hf e * bond s e) = (∑ e ∈ ghsvp_vertexEdges G.edgeFinset A, (2 * K e) * bond (fun x => s (some x)) e) + spin s none * ∑ x ∈ A, (2 * hf x) * spin s (some x) := by
-- proof
  apply StatMech.Ising.ghsi_fieldSet_couplingSum G K hf A s

/--
[ghsi_fieldSet_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsi_fieldSet_weight_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {A : Finset V}
  {s : ConfigSpace (Option V)}
-- given
  (hf : V → ℝ) :
-- imply
  wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A)) (ghsiGhostCoupling K hf) (fun _ => 0) s = wJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e) (fun x => if x ∈ A then (2 * hf x) * spin s none else 0) (fun x => s (some x)) := by
-- proof
  apply StatMech.Ising.ghsi_fieldSet_weight_eq G K hf A s

/--
[ghsi_someSet_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsi_someSet_weight_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {A : Finset V}
  {s : ConfigSpace (Option V)}
-- given
  (hf : V → ℝ) :
-- imply
  wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A)) (ghsiGhostCoupling K hf) (fun _ => 0) s = wJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e) (fun _ => 0) (fun x => s (some x)) := by
-- proof
  apply StatMech.Ising.ghsi_someSet_weight_eq G K hf A s

/--
[ghsi_vertexZ_fieldSet_eq_two_mul_tZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsi_vertexZ_fieldSet_eq_two_mul_tZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf) (ghsvp_fieldSet A) = 2 * ghsiTZ G K hf A := by
-- proof
  apply StatMech.Ising.ghsi_vertexZ_fieldSet_eq_two_mul_tZ G K hf A

/--
[ghsi_vertexZ_someSet_eq_two_mul_uZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsi_vertexZ_someSet_eq_two_mul_uZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf) (ghsvp_someSet A) = 2 * ghsiUZ G K A := by
-- proof
  apply StatMech.Ising.ghsi_vertexZ_someSet_eq_two_mul_uZ G K hf A

/--
[ghsiSubsetMass_eq_four_mul_tZ_uZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsiSubsetMass_eq_four_mul_tZ_uZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hf : V → ℝ) :
-- imply
  ghsiSubsetMass G K hf A = 4 * (ghsiTZ G K hf A * ghsiUZ G K Aᶜ) := by
-- proof
  apply StatMech.Ising.ghsiSubsetMass_eq_four_mul_tZ_uZ G K hf A

/--
[ghsiSubsetMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsiSubsetMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hf : V → ℝ) :
-- imply
  0 ≤ ghsiSubsetMass G K hf A := by
-- proof
  apply StatMech.Ising.ghsiSubsetMass_nonneg G K hf A

/--
[ghsiSubsetMass_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean)
-/
@[path]
private lemma ghsiSubsetMass_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {K : Sym2 V → ℝ}
  {A B : Finset V}
-- given
  (hf : V → ℝ)
  (hK : ∀ e, 0 ≤ K e)
  (hhf : ∀ x, 0 ≤ hf x) :
-- imply
  ghsiSubsetMass G K hf A * ghsiSubsetMass G K hf B ≤ ghsiSubsetMass G K hf (A ∪ B) * ghsiSubsetMass G K hf (A ∩ B) := by
-- proof
  apply StatMech.Ising.ghsiSubsetMass_logSupermodular G K hf hK hhf A B


-- created on 2026-10-23
