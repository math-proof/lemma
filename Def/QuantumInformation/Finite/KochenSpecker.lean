/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/KochenSpecker.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Tactic.FinCases


namespace MathlibExt.QuantumInformation.Finite.KochenSpeckerWanted

def w : Fin 35 → Fin 3 → ℤ :=
  ![![0, 0, 1], ![0, 1, -2], ![0, 1, -1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 2, -1],
    ![0, 2, 1], ![1, -2, 0], ![1, -2, 1], ![1, -1, -2], ![1, -1, -1], ![1, -1, 0], ![1, -1, 1],
    ![1, 0, -2], ![1, 0, -1], ![1, 0, 0], ![1, 0, 1], ![1, 1, -2], ![1, 1, -1], ![1, 1, 0],
    ![1, 1, 1], ![1, 2, -2], ![1, 2, -1], ![1, 2, 0], ![1, 2, 2], ![2, -2, -1], ![2, -2, 1],
    ![2, -1, 0], ![2, -1, 1], ![2, 0, 1], ![2, 1, -2], ![2, 1, 0], ![2, 1, 1], ![2, 1, 2]]

def x (i : Fin 35) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun j => ((w i j : ℤ) : ℝ))

noncomputable def v (i : Fin 35) : EuclideanSpace ℝ (Fin 3) := (‖x i‖⁻¹) • (x i)

end MathlibExt.QuantumInformation.Finite.KochenSpeckerWanted
