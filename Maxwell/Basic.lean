/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Basic objects: Maxwell's three-space, fields, stresses, and the 4π convention

Everything here is bookkeeping for Maxwell's own notation in the *Treatise on Electricity and
Magnetism* (1st ed. 1873; 2nd ed. 1881). No physical claim is made in this file.

* Space is `Fin 3 → ℝ` with Maxwell's axes `x, y, z` as indices `0, 1, 2`.
* A field (electromotive force `E`, displacement `D`, magnetic force `H`, magnetic induction `B`)
  is a map `Vec3 → Vec3`. The four are kept as **separate** arguments everywhere; nothing in this
  library identifies `B` with `H` or `D` with `E` except under an explicitly named hypothesis.
* Units are the Treatise's (electrostatic or electromagnetic measure, with explicit factors of
  `4π`, e.g. `4π D = K E`, `B = H + 4π I`, `4π J = curl H`). Nothing is converted to SI.
* A stress is a `3 × 3` real matrix that is **not** assumed symmetric, following Treatise 1873,
  vol. II, Art. 641 (p. 253): "`P_hk`, where the first suffix, h, indicates that the normal to the
  surface on which the stress is supposed to act is parallel to the axis of h, and the second
  suffix, k, indicates that the direction of the stress with which the part of the body on the
  positive side of the surface acts on the part on the negative side is parallel to the axis of
  k." Positive diagonal entries are tensions, negative ones pressures (Art. 108). This Art. 641
  convention is used throughout, including for the 1873 electrostatic chapter: 1873 Art. 108's
  verbal convention ("urge the parts on the positive side") reads the other way, but his
  face-by-face computation gives the same `ξ = ∑_h d p_hx/dx_h`, so Art. 641's convention
  reproduces Art. 108's eqs. (7)–(10) (`art108_force`).

Local source text: `/workspace/maxwell_reread/n_electricandmagne02maxwrich.txt` (1873, vol. II).
-/

namespace Maxwell

open Matrix

/-- A point or vector of Maxwell's three-dimensional space, axes `x, y, z = 0, 1, 2`. -/
abbrev Vec3 := Fin 3 → ℝ

/-- A stress referred to unit of area, `P h k` in the convention of Treatise 1873, Art. 641
(p. 253). Not assumed symmetric. -/
abbrev Stress := Matrix (Fin 3) (Fin 3) ℝ

/-- The square of the numerical value of a vector, `X² + Y² + Z²`. -/
def sq (v : Vec3) : ℝ := v ⬝ᵥ v

theorem sq_eq (v : Vec3) : sq v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [sq, dotProduct, Fin.sum_univ_three]; ring

theorem sq_nonneg' (v : Vec3) : 0 ≤ sq v := by
  rw [sq_eq]; positivity

/-- Kronecker delta as a real number. -/
def δ (h k : Fin 3) : ℝ := if h = k then 1 else 0

/-- The unit vector along the axis `i`. -/
def axis (i : Fin 3) : Vec3 := Pi.single i 1

/-- Partial derivative `d/dx_i` of a scalar function at a point, as a Fréchet derivative applied
to the unit vector of the axis. -/
noncomputable def pd (i : Fin 3) (f : Vec3 → ℝ) (x : Vec3) : ℝ := fderiv ℝ f x (axis i)

/-- Divergence `dX/dx + dY/dy + dZ/dz` (Maxwell's "convergence" is its negative). -/
noncomputable def div (F : Vec3 → Vec3) (x : Vec3) : ℝ := ∑ i, pd i (fun y => F y i) x

/-- Curl, in the right-handed sense of Treatise 1873, vol. II, Art. 607 equations (E):
`4π u = dγ/dy − dβ/dz`, etc. -/
noncomputable def curl (F : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  ![pd 1 (fun y => F y 2) x - pd 2 (fun y => F y 1) x,
    pd 2 (fun y => F y 0) x - pd 0 (fun y => F y 2) x,
    pd 0 (fun y => F y 1) x - pd 1 (fun y => F y 0) x]

/-- Gradient `(dΨ/dx, dΨ/dy, dΨ/dz)`. -/
noncomputable def grad (f : Vec3 → ℝ) (x : Vec3) : Vec3 := fun i => pd i f x

/-- Resultant force per unit volume of a stress field on an element `dx dy dz`
(Treatise 1873, vol. I, Art. 108, p. 130, and vol. II, Art. 641, eq. (13), p. 254):
`X = d/dx P_xx + d/dy P_yx + d/dz P_zx`. -/
noncomputable def stressForce (P : Vec3 → Stress) (x : Vec3) : Vec3 :=
  fun k => ∑ h, pd h (fun y => P y h k) x

/-- Force per unit area exerted across a surface element with normal `n` by the medium on the
positive side (Art. 641 convention): `k`-component `∑_h n_h P_hk`. -/
def traction (P : Stress) (n : Vec3) : Vec3 := fun k => ∑ h, n h * P h k

/-- The couple per unit volume of a stress (Treatise 1873, vol. II, Art. 641, eq. (14), p. 254):
`L = P_yz − P_zy`, and cyclically. -/
def couple (P : Stress) : Vec3 := ![P 1 2 - P 2 1, P 2 0 - P 0 2, P 0 1 - P 1 0]

/-- Maxwell's `4π`. -/
noncomputable abbrev fourPi : ℝ := 4 * Real.pi

/-! ### Calculus helpers (pure bookkeeping) -/

theorem pd_mul {f g : Vec3 → ℝ} {x : Vec3} (i : Fin 3) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  unfold pd
  have := fderiv_mul hf hg
  simp only [Pi.mul_def] at this
  rw [this]; simp; ring

theorem pd_add {f g : Vec3 → ℝ} {x : Vec3} (i : Fin 3) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  unfold pd; rw [show (fun y => f y + g y) = f + g from rfl, fderiv_add hf hg]; rfl

theorem pd_sub {f g : Vec3 → ℝ} {x : Vec3} (i : Fin 3) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  unfold pd; rw [show (fun y => f y - g y) = f - g from rfl, fderiv_sub hf hg]; rfl

theorem pd_const_mul {f : Vec3 → ℝ} {x : Vec3} (i : Fin 3) (c : ℝ) (hf : DifferentiableAt ℝ f x) :
    pd i (fun y => c * f y) x = c * pd i f x := by
  unfold pd; rw [fderiv_const_mul hf]; rfl

theorem pd_neg {f : Vec3 → ℝ} {x : Vec3} (i : Fin 3) :
    pd i (fun y => - f y) x = - pd i f x := by
  unfold pd; rw [show (fun y => - f y) = -f from rfl, fderiv_neg]; rfl

theorem pd_const (i : Fin 3) (c : ℝ) (x : Vec3) : pd i (fun _ => c) x = 0 := by
  simp [pd]

/-! ### Second derivatives of a potential (symmetric for a `C²` potential) -/

theorem differentiableAt_fderiv_of_contDiffAt {Ψ : Vec3 → ℝ} {x : Vec3}
    (hΨ : ContDiffAt ℝ 2 Ψ x) : DifferentiableAt ℝ (fderiv ℝ Ψ) x :=
  (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

theorem differentiableAt_pd {Ψ : Vec3 → ℝ} {x : Vec3} (hΨ : ContDiffAt ℝ 2 Ψ x) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => pd j Ψ y) x :=
  (differentiableAt_fderiv_of_contDiffAt hΨ).clm_apply (differentiableAt_const _)

theorem pd_pd {Ψ : Vec3 → ℝ} {x : Vec3} (hΨ : ContDiffAt ℝ 2 Ψ x) (i j : Fin 3) :
    pd i (fun y => pd j Ψ y) x = fderiv ℝ (fderiv ℝ Ψ) x (axis i) (axis j) := by
  unfold pd
  rw [fderiv_clm_apply (differentiableAt_fderiv_of_contDiffAt hΨ) (differentiableAt_const _)]
  simp

theorem pd_pd_comm {Ψ : Vec3 → ℝ} {x : Vec3} (hΨ : ContDiffAt ℝ 2 Ψ x) (i j : Fin 3) :
    pd i (fun y => pd j Ψ y) x = pd j (fun y => pd i Ψ y) x := by
  rw [pd_pd hΨ, pd_pd hΨ]
  exact (hΨ.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])) _ _

end Maxwell
