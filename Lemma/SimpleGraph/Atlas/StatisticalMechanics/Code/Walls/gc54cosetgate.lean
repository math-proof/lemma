import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc54cosetgate.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc54_gate_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_gate_monotone_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {m₁ m₂ : Finset ι}
  {x g : W}
-- given
  (h : m₁ ⊆ m₂)
  (hgate : connK ends (K ∪ m₁) x g) :
-- imply
  connK ends (K ∪ m₂) x g := by
-- proof
  apply StatMech.Walls.gc54_gate_monotone ends K h hgate

/--
[gc54_gate_disjoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_gate_disjoint_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {L P₀ : Finset ι}
  {x g : W}
-- given
  (hdisj : Disjoint L P₀)
  (hgate : connK ends (K ∪ L) x g) :
-- imply
  connK ends (K ∪ (L ∆ P₀)) x g := by
-- proof
  apply StatMech.Walls.gc54_gate_disjoint_eq ends K hdisj hgate

/--
[gc54_LblockSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_LblockSet_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x g : W} :
-- imply
  gc51_LblockSet ends K o x g = (univ \ K).powerset.filter (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ L) x g) := by
-- proof
  apply StatMech.Walls.gc54_LblockSet_eq ends K o x g

/--
[gc54_cosetGateBlock_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_cosetGateBlock_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K P₀ : Finset ι}
  {o x g : W} :
-- imply
  gc53_cosetGateBlock ends K P₀ o x g = (univ \ K).powerset.filter (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ (L ∆ P₀)) x g) := by
-- proof
  apply StatMech.Walls.gc54_cosetGateBlock_eq ends K P₀ o x g

/--
[gc54_shift_mem_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_shift_mem_A_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K C L : Finset ι}
  {o x g : W}
-- given
  (hCV : C ⊆ univ \ K)
  (hCsrc : sources ends C = (∅ : Finset W))
  (hL : L ∈ gc51_LblockSet ends K o x g) :
-- imply
  (L ∆ C) ⊆ univ \ K ∧ sources ends (L ∆ C) = (∅ : Finset W) := by
-- proof
  apply StatMech.Walls.gc54_shift_mem_A ends hCV hCsrc hL

/--
[gc54_shift_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_shift_injOn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {C : Finset ι}
  {s : Finset (Finset ι)} :
-- imply
  Set.InjOn (fun L => L ∆ C) (s : Set (Finset ι)) := by
-- proof
  apply StatMech.Walls.gc54_shift_injOn C s

/--
[gc54_lblock_le_cosetGate_of_gateShiftInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_lblock_le_cosetGate_of_gateShiftInjection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K P₀ : Finset ι}
  {o x g : W}
-- given
  (h : gc54_GateShiftInjection ends K P₀ o x g) :
-- imply
  #(gc51_LblockSet ends K o x g) ≤ #(gc53_cosetGateBlock ends K P₀ o x g) := by
-- proof
  apply StatMech.Walls.gc54_lblock_le_cosetGate_of_gateShiftInjection ends K P₀ h

/--
[gc54_gateShiftInjection_of_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_gateShiftInjection_of_identity_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K P₀ : Finset ι}
  {o x g : W}
-- given
  (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L P₀) :
-- imply
  gc54_GateShiftInjection ends K P₀ o x g := by
-- proof
  apply StatMech.Walls.gc54_gateShiftInjection_of_identity ends K P₀ hdisj

/--
[gc54_cosetGateDom_of_gateShiftInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_cosetGateDom_of_gateShiftInjection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), ∀ P₀ ⊆ univ \ K, sources ends P₀ = ({y, g} : Finset W) → gc54_GateShiftInjection ends K P₀ o x g) :
-- imply
  gc53_CosetGateDom ends o x y g := by
-- proof
  apply StatMech.Walls.gc54_cosetGateDom_of_gateShiftInjection ends h

/--
[gc54_countIneq_of_gateShiftInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_countIneq_of_gateShiftInjection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), ∀ P₀ ⊆ univ \ K, sources ends P₀ = ({y, g} : Finset W) → gc54_GateShiftInjection ends K P₀ o x g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc54_countIneq_of_gateShiftInjection ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc54_witness_gateShiftInjection_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_witness_gateShiftInjection_K13_eq
  {P₀ : Finset (Fin 4)} :
-- imply
  gc54_GateShiftInjection gc49_witnessEnds ({1, 3} : Finset (Fin 4)) P₀ 0 1 3 := by
-- proof
  apply StatMech.Walls.gc54_witness_gateShiftInjection_K13 P₀

/--
[gc54_witness_gateShiftInjection_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_witness_gateShiftInjection_K23_eq
  {P₀ : Finset (Fin 4)} :
-- imply
  gc54_GateShiftInjection gc49_witnessEnds ({2, 3} : Finset (Fin 4)) P₀ 0 1 3 := by
-- proof
  apply StatMech.Walls.gc54_witness_gateShiftInjection_K23 P₀

/--
[gc54_witness_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_witness_cosetGateDom_eq :
-- imply
  gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc54_witness_cosetGateDom

/--
[gc54_witness_perKCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean)
-/
@[path]
private lemma gc54_witness_perKCount_eq :
-- imply
  gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc54_witness_perKCount


-- created on 2026-10-23
