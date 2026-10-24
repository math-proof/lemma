/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Graph/MaxFlowMinCut.lean -/


import sympy.atlas.Combinatorics.Graph.MaxFlowMinCut
import Lemma.Finset.Graph.MaxFlowMinCut

namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

example : flowValue (0 : Fin 2) (fun u v => if u = 0 ∧ v = 1 then (3 : ℝ) else 0) = 3 := by
  simp [flowValue]

example : cutCapacity (fun u v : Fin 2 => if u = 0 ∧ v = 1 then (5 : ℝ) else 0) {0} = 5 := by
  have : (Finset.univ : Finset (Fin 2)) \ {0} = {1} := by decide
  simp [cutCapacity, this]

example {V : Type*} [Fintype V] [DecidableEq V] (cap : V → V → ℝ) (s t : V) (hst : s ≠ t)
    (f : V → V → ℝ) (hf : IsFeasibleFlow cap s t f) :
    flowValue s f ≤ cutCapacity cap {s} :=
  flowValue_le_cutCapacity cap s t f hf {s} ⟨Finset.mem_singleton_self s, by simpa using hst.symm⟩

example {V : Type*} [Fintype V] [DecidableEq V] (cap : V → V → ℝ) (hcap : ∀ u v, 0 ≤ cap u v)
    (s t : V) (hst : s ≠ t) :
    ∃ f S, IsFeasibleFlow cap s t f ∧ IsSTCut s t S ∧ flowValue s f = cutCapacity cap S := by
  obtain ⟨f, hf, -, -, S, hS, h⟩ := max_flow_min_cut cap hcap s t hst
  exact ⟨f, S, hf, hS, h⟩

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted
