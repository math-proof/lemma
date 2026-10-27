import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Abbrev.Analysis.InnerProductSpace.EuclideanVec


/-!
# Translational kinematics

Basic position / displacement / velocity vocabulary aligned with
[`sympy.physics.vector`](https://docs.sympy.org/latest/modules/physics/vector/api/kinematics.html)
and the usual Cartesian / polar textbook identities:

1. \(\vec{r}(t)=r(t)\,\hat{r}(t)\) with \(r=|\vec{r}|\)
2. \(\Delta\vec{r}=\vec{r}(t+\Delta t)-\vec{r}(t)\)
3. \(\vec{v}=d\vec{r}/dt=\lim_{\Delta t\to 0}\Delta\vec{r}/\Delta t\)
4. Cartesian components and \(v=|\vec{v}|=\sqrt{v_x^2+v_y^2+v_z^2}\)
5. Polar product rule \(\vec{v}=\dot r\,\hat{r}+r\,d\hat{r}/dt\)
6–8. Polar unit vectors \(\hat{r}(\theta),\hat{\theta}(\theta)\) with
   \(d\hat{r}/d\theta=\hat{\theta}\) and \(d\hat{\theta}/d\theta=-\hat{r}\)
9. Chain rule \(d\hat{r}(\theta(t))/dt=\dot\theta\,\hat{\theta}\)
10. Polar acceleration
    \(\vec{a}=(\ddot\rho-\rho\dot\theta^2)\hat{r}+(\rho\ddot\theta+2\dot\rho\dot\theta)\hat{\theta}\)
11. Uniform circular motion \(\vec{v}=\rho_0\omega\hat{\theta}\), \(\vec{a}=-\rho_0\omega^2\hat{r}\)
12. Inverse-square / angular momentum \(h=\rho^2\dot\theta\)
13. Binet transform \(w=1/r\), \(w''+w=Cm/J^2\), orbit \(1/r=A\cos\theta+Cm/J^2\)
14. Central potential \(E_p=C/r\), mechanical energy, eccentricity / semi-latus rectum,
    and Kepler II (constant areal speed \(J/(2m)\))
-/

/-- Time-parametrized position path \(\vec{r}(t)\) in Euclidean \(d\)-space. -/
abbrev Position (d : ℕ) := ℝ → EuclideanVec d

