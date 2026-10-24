import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardUnicyclicAssembly
open StatMech StatMech.FrontierA


/--
[kw_det_one_sub_blockTriangular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnicyclicAssembly.lean)
-/
@[path]
private lemma kw_det_one_sub_blockTriangular_eq
  [Fintype D]
  [DecidableEq D]
  [Fintype Block]
  [DecidableEq Block]
  [LinearOrder Block]
  {transition : Matrix D D ℂ}
-- given
  (block : D -> Block)
  (htriangular : transition.BlockTriangular block) :
-- imply
  (1 - transition).det = ∏ k : Block, (1 - transition.toSquareBlock block k).det := by
-- proof
  apply StatMech.FrontierA.kw_det_one_sub_blockTriangular transition block htriangular

/--
[kw_one_sub_acyclicCycleExtension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnicyclicAssembly.lean)
-/
@[path]
private lemma kw_one_sub_acyclicCycleExtension_eq
  [Fintype Incoming]
  [DecidableEq Incoming]
  [Fintype Core]
  [DecidableEq Core]
  [Fintype Outgoing]
  [DecidableEq Outgoing]
  {incoming : Matrix Incoming Incoming ℂ}
  {incomingToRest : Matrix Incoming (Core ⊕ Outgoing) ℂ}
  {core : Matrix Core Core ℂ}
  {coreToOutgoing : Matrix Core Outgoing ℂ}
  {outgoing : Matrix Outgoing Outgoing ℂ} :
-- imply
  1 - kwAcyclicCycleExtension incoming incomingToRest core coreToOutgoing outgoing = Matrix.fromBlocks (1 - incoming) (-incomingToRest) 0 (Matrix.fromBlocks (1 - core) (-coreToOutgoing) 0 (1 - outgoing)) := by
-- proof
  apply StatMech.FrontierA.kw_one_sub_acyclicCycleExtension incoming incomingToRest core coreToOutgoing outgoing

/--
[kw_det_acyclicCycleExtension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnicyclicAssembly.lean)
-/
@[path]
private lemma kw_det_acyclicCycleExtension_eq
  [Fintype Incoming]
  [DecidableEq Incoming]
  [Fintype Core]
  [DecidableEq Core]
  [Fintype Outgoing]
  [DecidableEq Outgoing]
  {incoming : Matrix Incoming Incoming ℂ}
  {incomingToRest : Matrix Incoming (Core ⊕ Outgoing) ℂ}
  {core : Matrix Core Core ℂ}
  {coreToOutgoing : Matrix Core Outgoing ℂ}
  {outgoing : Matrix Outgoing Outgoing ℂ}
-- given
  (hIncoming : IsNilpotent incoming)
  (hOutgoing : IsNilpotent outgoing) :
-- imply
  (1 - kwAcyclicCycleExtension incoming incomingToRest core coreToOutgoing outgoing).det = (1 - core).det := by
-- proof
  apply StatMech.FrontierA.kw_det_acyclicCycleExtension incoming incomingToRest core coreToOutgoing outgoing hIncoming hOutgoing

/--
[kacWard_acyclic_extension_of_phase_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnicyclicAssembly.lean)
-/
@[path]
private lemma kacWard_acyclic_extension_of_phase_sign_eq
  [Fintype Incoming]
  [DecidableEq Incoming]
  [Fintype Outgoing]
  [DecidableEq Outgoing]
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {incoming : Matrix Incoming Incoming ℂ}
  {incomingToRest : Matrix Incoming ((E × Bool) ⊕ Outgoing) ℂ}
  {outgoing : Matrix Outgoing Outgoing ℂ}
  {coreToOutgoing : Matrix (E × Bool) Outgoing ℂ}
  {sigma : Equiv.Perm E}
-- given
  (edgeWeight : E -> ℂ)
  (phase : Bool -> E -> ℂ)
  (hIncoming : IsNilpotent incoming)
  (hOutgoing : IsNilpotent outgoing)
  (hcycle : sigma.IsCycle)
  (hfree : ∀ i, sigma i ≠ i)
  (hphase : ∀ b, ∏ i, phase b i = -1) :
-- imply
  (1 - kwAcyclicCycleExtension incoming incomingToRest (kwTwoOrientationCycleTransition sigma (fun b i => edgeWeight i * phase b i)) coreToOutgoing outgoing).det = (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_acyclic_extension_of_phase_sign incoming incomingToRest outgoing coreToOutgoing sigma edgeWeight phase hIncoming hOutgoing hcycle hfree hphase

/--
[kacWard_rectilinear_acyclic_extension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnicyclicAssembly.lean)
-/
@[path]
private lemma kacWard_rectilinear_acyclic_extension_eq
  [Fintype Incoming]
  [DecidableEq Incoming]
  [Fintype Outgoing]
  [DecidableEq Outgoing]
  {n : ℕ}
  [NeZero n]
  {incoming : Matrix Incoming Incoming ℂ}
  {incomingToRest : Matrix Incoming ((Fin n × Bool) ⊕ Outgoing) ℂ}
  {outgoing : Matrix Outgoing Outgoing ℂ}
  {coreToOutgoing : Matrix (Fin n × Bool) Outgoing ℂ}
  {omega : ℂ}
-- given
  (hIncoming : IsNilpotent incoming)
  (hOutgoing : IsNilpotent outgoing)
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (d : Fin n -> Fin 4)
  (hclosed : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0)
  (hsimple : Function.Injective (StatMech.Onsager.BaseCase.pos d))
  (hn : 3 ≤ n)
  (hnu : ∀ i, d (i + 1) ≠ d i + 2)
  (edgeWeight : Fin n -> ℂ) :
-- imply
  (1 - kwAcyclicCycleExtension incoming incomingToRest (kwTwoOrientationCycleTransition (finRotate n) (fun _ i => edgeWeight i * StatMech.Onsager.ons_turnW omega (d i) (d (i + 1)))) coreToOutgoing outgoing).det = (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_rectilinear_acyclic_extension incoming incomingToRest outgoing coreToOutgoing hIncoming hOutgoing omega homega hI d hclosed hsimple hn hnu edgeWeight


-- created on 2026-10-23
