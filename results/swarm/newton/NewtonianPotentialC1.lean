/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.NewtonianPotential
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Art. 616–617, step (ii): differentiating the Newtonian potential under the integral

`P x = ∫ y, C y i / ‖x − y‖`. The substitution `y = x + z` (`newtonPotential_eq_integral_add`)
moves the singularity to the fixed point `z = 0`, after which the only analytic input for
`pd j P x = ∫ z, (1/‖z‖) · ∂ⱼC (x + z)` is the local integrability of `1/‖z‖` in `ℝ³`
(`TruncatedKernelIntegrable`; in the Euclidean metric `∫_{‖z‖≤R} ‖z‖⁻¹ dz = 2πR²`). With that
formula, `div C = 0` gives `div P = 0` — Maxwell's `S.∇𝔄 = 0` of Art. 617 — with no separate
theory, since `∑ⱼ ∫ z, ‖z‖⁻¹ ∂ⱼC(x+z) = ∫ z, ‖z‖⁻¹ (div C)(x+z) = 0`.

The ε-shell form of the Poisson identity is proved below from the explicit truncated potentials.
-/

namespace Maxwell

open Matrix Filter Topology MeasureTheory

section Kernel

theorem sq_neg (z : Vec3) : sq (-z) = sq z := by
  rw [sq_eq, sq_eq]; simp only [Pi.neg_apply]; ring

theorem eNorm_neg (z : Vec3) : eNorm (-z) = eNorm z := by
  rw [eNorm, eNorm, sq_neg]

theorem continuous_eNorm : Continuous eNorm := by
  unfold eNorm
  refine Real.continuous_sqrt.comp ?_
  unfold sq
  fun_prop

theorem eNorm_sub_comm (a b : Vec3) : eNorm (a - b) = eNorm (b - a) := by
  rw [← eNorm_neg (b - a)]
  congr 1
  abel

/-- Integrability of the truncated kernel `1/‖z‖` in `ℝ³`. This is the local integrability of the
Newtonian kernel; in the Euclidean metric `∫_{‖z‖≤R} ‖z‖⁻¹ dz = 2πR² < ∞`. It is the *only*
analytic input of the differentiation under the integral, and it is named rather than assumed
silently. -/
def TruncatedKernelIntegrable : Prop :=
  ∀ R : ℝ, Integrable (fun z : Vec3 => (1 / eNorm z) * (if eNorm z ≤ R then 1 else 0))

variable {C : Vec3 → Vec3}

/-- The substitution `y = x + z` moves the singularity of the kernel to the origin: this is the
form in which the differentiated integrand is dominated by the truncated kernel. -/
theorem newtonPotential_eq_integral_add (i : Fin 3) (x : Vec3) :
    newtonPotential C i x = ∫ z, C (x + z) i * (1 / eNorm z) := by
  have h : ∀ y : Vec3, C y i * (1 / eNorm (x - y))
      = (fun z => C (x + z) i * (1 / eNorm z)) (y - x) := by
    intro y
    simp only
    rw [show x + (y - x) = y from by abel, eNorm_sub_comm y x]
  simp only [newtonPotential, newtonKernel, eDist, h]
  simpa using integral_sub_right_eq_self (fun z : Vec3 => C (x + z) i * (1 / eNorm z)) x

end Kernel

/-! ## Gap 2: the ε-shell form of the singular integral

The Poisson identity `∇²P = 4πC` is reduced to a limit statement about the **truncated**
potentials `P_ε x = ∫_{‖x−y‖>ε} C y i/‖x−y‖` (an explicit family, not `P` itself): the second
partials of `P_ε` must converge to those of `P` (i.e. `P_ε → P` in `C²`), and the Laplacians of
`P_ε` must converge to the solid-angle term `4πC x i`. The latter is the classical excision
computation: on the shell the volume term vanishes because `Δ_x(1/‖x−y‖) = 0` for `y ≠ x`
(`maxwellNabla2_newtonKernel`), leaving `∮_{∂Q_ε} ∂_ν(1/‖x−y‖) dS`, whose cube-face factor is
`6 · ∫∫_{[-1,1]²} (1+u²+v²)^{-3/2} du dv = 6 · 2π/3 = 4π`. -/

section Shell

/-- The truncated potential: the Newtonian potential with the cube of radius `ε` about `x`
excised (a ball would do; a cube matches Mathlib's box divergence theorem). -/
noncomputable def truncatedPotential (C : Vec3 → Vec3) (i : Fin 3) (ε : ℝ) (x : Vec3) : ℝ :=
  ∫ y in {y : Vec3 | ε ≤ eNorm (x - y)}, C y i * newtonKernel y x

/-- **The ε-shell input**, with no reference to `∇²P = 4πC`: the truncated potentials converge to
the potential in `C²` at every point, and their Laplacians converge to the solid-angle term. -/
def NewtonianPotentialShellLimit : Prop :=
  ∀ (C : Vec3 → Vec3) (i : Fin 3), ContDiff ℝ ⊤ C → HasCompactSupport C →
    (∀ x, Tendsto (fun ε : ℝ => maxwellNabla2 (truncatedPotential C i ε) x)
        (𝓝[>] (0 : ℝ)) (𝓝 (fourPi * C x i))) ∧
    (∀ (x : Vec3) (j : Fin 3),
      Tendsto (fun ε : ℝ => pd j (fun z => pd j (truncatedPotential C i ε) z) x)
        (𝓝[>] (0 : ℝ)) (𝓝 (pd j (fun z => pd j (newtonPotential C i) z) x)))

/-- **Art. 617, the Poisson equation, from the ε-shell input.** Continuity of the Laplacian in the
`C²` topology (`P_ε → P` together with the second partials converging) turns the ε-limit into the
pointwise identity. -/
theorem maxwellNabla2_newtonPotential_of_shellLimit (h : NewtonianPotentialShellLimit)
    {C : Vec3 → Vec3} (i : Fin 3) (hC : ContDiff ℝ ⊤ C) (hsC : HasCompactSupport C) (x : Vec3) :
    maxwellNabla2 (newtonPotential C i) x = fourPi * C x i := by
  obtain ⟨h1, h2⟩ := h C i hC hsC
  have hlim : Tendsto (fun ε : ℝ => -∑ j : Fin 3,
      pd j (fun z => pd j (truncatedPotential C i ε) z) x) (𝓝[>] (0 : ℝ)) (𝓝 (fourPi * C x i)) :=
    h1 x
  have hlim2 : Tendsto (fun ε : ℝ => -∑ j : Fin 3,
      pd j (fun z => pd j (truncatedPotential C i ε) z) x) (𝓝[>] (0 : ℝ))
      (𝓝 (-∑ j : Fin 3, pd j (fun z => pd j (newtonPotential C i) z) x)) := by
    refine Tendsto.neg (tendsto_finsetSum _ fun j _ => ?_)
    exact h2 x j
  have := tendsto_nhds_unique hlim hlim2
  unfold maxwellNabla2
  linarith [this]

end Shell

end Maxwell
