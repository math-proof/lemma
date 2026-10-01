import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import sympy.vector.euclidean

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

/-- Radial distance \(r=|\vec{r}|\). -/
noncomputable def radial {d : ℕ} (r : Position d) (t : ℝ) : ℝ := ‖r t‖

/-- Unit radial \(\hat{r}=r^{-1}\vec{r}\) (algebraically defined for all \(t\)). -/
noncomputable def unit_radial {d : ℕ} (r : Position d) (t : ℝ) : EuclideanVec d :=
  (‖r t‖)⁻¹ • r t

/-- Displacement \(\Delta\vec{r}(t)=\vec{r}(t+\Delta t)-\vec{r}(t)\). -/
def displacement {d : ℕ} (r : Position d) (t Δt : ℝ) : EuclideanVec d :=
  r (t + Δt) - r t

/-- Instantaneous velocity \(\vec{v}=d\vec{r}/dt\) (Mathlib `deriv`). -/
noncomputable def velocity {d : ℕ} (r : Position d) (t : ℝ) : EuclideanVec d :=
  deriv r t

/-- Speed \(v=|\vec{v}|\). -/
noncomputable def speed {d : ℕ} (r : Position d) (t : ℝ) : ℝ :=
  ‖velocity r t‖

/-! ## Plane polar unit vectors -/

/--
Polar radial unit vector
\(\hat{r}(\theta)=(\cos\theta)\,\hat{x}+(\sin\theta)\,\hat{y}\).
-/
noncomputable def polar_radial (θ : ℝ) : EuclideanVec 2 :=
  WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

/--
Polar angular unit vector
\(\hat{\theta}(\theta)=(-\sin\theta)\,\hat{x}+(\cos\theta)\,\hat{y}\),
so \(\hat{\theta}\perp\hat{r}\).
-/
noncomputable def polar_angular (θ : ℝ) : EuclideanVec 2 :=
  WithLp.toLp 2 ![-Real.sin θ, Real.cos θ]

/-- Plane polar path \(\vec{r}(t)=\rho(t)\,\hat{r}(\theta(t))\). -/
noncomputable def polar_position (ρ θ : ℝ → ℝ) : Position 2 :=
  fun t => ρ t • polar_radial (θ t)

/-- Instantaneous acceleration \(\vec{a}=d\vec{v}/dt=d^2\vec{r}/dt^2\). -/
noncomputable def acceleration {d : ℕ} (r : Position d) (t : ℝ) : EuclideanVec d :=
  deriv (velocity r) t

/--
Specific angular momentum (plane polar scalar)
\(h=\rho^2\dot\theta\) (so \(J=m\,h\)).
-/
noncomputable def specific_angular_momentum (ρ θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (ρ t)^2 * deriv θ t

/-- Angular momentum \(J=m\rho^2\dot\theta\). -/
noncomputable def angular_momentum (m : ℝ) (ρ θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  m * specific_angular_momentum ρ θ t

/-! ## Binet / orbit equation (radius as a function of angle) -/

/--
Reciprocal radius \(w(\theta)=1/r(\theta)\) used in the Binet transformation.
Here `r` is the polar radius as a function of the polar angle.
-/
noncomputable def binet_w (r : ℝ → ℝ) (φ : ℝ) : ℝ :=
  (r φ)⁻¹

/--
Kepler / inverse-square orbit ansatz (phase \(\phi=0\)):
\(1/r=A\cos\theta+cm/J^2\).
-/
noncomputable def kepler_orbit_reciprocal (A c m J : ℝ) (φ : ℝ) : ℝ :=
  A * Real.cos φ + c * m / J ^ 2

/--
Formal radial acceleration expressed in the angle domain (Binet substitution),
using conserved \(J=m\rho^2\dot\theta\):
\[\ddot r=\frac{J^2}{m^2 r^4}\left(r''-\frac{2}{r}(r')^2\right).\]
-/
noncomputable def rddot_of_angle (r : ℝ → ℝ) (J m φ : ℝ) : ℝ :=
  J ^ 2 / (m ^ 2 * (r φ) ^ 4) *
    (deriv (deriv r) φ - 2 / (r φ) * (deriv r φ) ^ 2)

/-! ## Central potential, energy, and Kepler orbit parameters -/

/--
Inverse-square central potential \(E_p=C/r\) (convention \(E_p\to 0\) as \(r\to\infty\)).
Here \(C>0\) is repulsive and \(C<0\) is attractive for \(\vec F=C\hat r/r^2\).
-/
noncomputable def central_potential (C r : ℝ) : ℝ :=
  C / r

/--
Mechanical energy for plane polar motion:
\(E=\frac12 m\|\vec v\|^2+C/\rho\).
-/
noncomputable def mechanical_energy (m C : ℝ) (ρ θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * m * ‖velocity (polar_position ρ θ) t‖ ^ 2 + C / ρ t

/--
Angle-domain energy using conserved \(J=m r^2\dot\theta\):
\[
E=\frac{J^2}{2m r^4}\left(\frac{dr}{d\theta}\right)^2+\frac{J^2}{2m r^2}+\frac{C}{r}.
\]
-/
noncomputable def mechanical_energy_of_angle (m C J : ℝ) (r : ℝ → ℝ) (φ : ℝ) : ℝ :=
  J ^ 2 / (2 * m * (r φ) ^ 4) * (deriv r φ) ^ 2 + J ^ 2 / (2 * m * (r φ) ^ 2) + C / r φ

/--
Orbit eccentricity
\(e=\sqrt{1+\dfrac{2EJ^2}{mC^2}}\).
-/
noncomputable def orbit_eccentricity (E m C J : ℝ) : ℝ :=
  Real.sqrt (1 + 2 * E * J ^ 2 / (m * C ^ 2))

/--
Semi-latus rectum \(p=-J^2/(Cm)\) for the signed force constant \(C\).
-/
noncomputable def semi_latus_rectum (C m J : ℝ) : ℝ :=
  -(J ^ 2) / (C * m)

/--
Areal speed \(ds/dt=J/(2m)\) (Kepler's second law for central forces).
-/
noncomputable def areal_speed (m : ℝ) (ρ θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  angular_momentum m ρ θ t / (2 * m)

/--
Signed Kepler reciprocal matching notes \(1/r=-Cm/J^2+A\cos\theta\):
`kepler_orbit_reciprocal A (-C) m J`.
-/
noncomputable def kepler_orbit_reciprocal_signed (A C m J : ℝ) : ℝ → ℝ :=
  kepler_orbit_reciprocal A (-C) m J
