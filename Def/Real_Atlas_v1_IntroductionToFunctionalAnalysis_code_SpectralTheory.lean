module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

@[expose] public section

open Function Set Filter Bornology Metric Pointwise Topology
open Module End
open MeasureTheory

/-! Local Atlas SpectralTheory wrappers (Real-only packaging).
Sympy SpectralTheory.lean is held broken (Lp / L2UnitInterval instances);
do not import it until sympy lake-clean. -/

namespace SpectralTheory

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A bounded linear operator $T : H \to H$ on a Hilbert space is *self-adjoint*
if $T = T^\ast$. This is a wrapper around Mathlib's `IsSelfAdjoint`. -/
def IsSelfAdjointOperator (T : H →L[𝕜] H) : Prop := IsSelfAdjoint T

/-- The Hilbert space $L^2([0,1])$ of square-integrable real-valued functions on
the unit interval, equipped with the restriction of Lebesgue measure to $[0,1]$. -/
noncomputable abbrev L2UnitInterval :=
  MeasureTheory.Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- The $k$-th orthonormal sine basis function on $[0,1]$:
$u_k(x) = \sqrt{2} \sin(k\pi x)$.
These form an orthonormal eigenbasis of the Green's operator with Dirichlet
boundary conditions on the unit interval. -/
noncomputable def sineBasisFun (k : ℕ+) : ℝ → ℝ :=
  fun x => Real.sqrt 2 * Real.sin (↑k * Real.pi * x)

/-- The $k$-th eigenvalue of the Green's operator on $[0,1]$ with Dirichlet
boundary conditions: $\lambda_k = \dfrac{1}{k^2 \pi^2}$. -/
noncomputable def greensEigenvalue (k : ℕ+) : ℝ := 1 / ((k : ℝ) ^ 2 * Real.pi ^ 2)

/-- The square root of the $k$-th eigenvalue of the Green's operator,
$\sqrt{\lambda_k} = \dfrac{1}{k\pi}$. This is the $k$-th eigenvalue of $A^{1/2}$. -/
noncomputable def greensEigenvalueSqrt (k : ℕ+) : ℝ := 1 / ((k : ℝ) * Real.pi)

/-- The square root $A^{1/2}$ of the Green's operator, defined via its action on the
orthonormal eigenbasis $\{b_k\}$: if $f = \sum_k c_k\, b_k$ where
$c_k = \langle b_k, f\rangle$, then
$A^{1/2} f = \sum_k \frac{1}{k\pi}\, c_k\, b_k$. -/
noncomputable def greensOperatorSqrt (b : HilbertBasis ℕ+ ℝ L2UnitInterval) :
    L2UnitInterval → L2UnitInterval :=
  fun f => ∑' (k : ℕ+), (greensEigenvalueSqrt k * inner (𝕜 := ℝ) (b k) f) • b k

/-- The Green's kernel for the Dirichlet Laplacian on $[0,1]$:
$G(x,t) = \min(x,t)\,(1 - \max(x,t))$.
The Green's operator $f \mapsto \int_0^1 G(x,t) f(t)\,dt$ is the inverse of
$-\frac{d^2}{dx^2}$ subject to $u(0)=u(1)=0$. -/
noncomputable def greensKernel (x t : ℝ) : ℝ :=
  min x t * (1 - max x t)

end SpectralTheory

end
