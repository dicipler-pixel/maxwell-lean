/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Electromotive force on a moving element (Treatise 1873, vol. II, Arts. 598–599)

Art. 598 (pp. 219–221), equations (B):
`P = c dy/dt − b dz/dt − dF/dt − dΨ/dx`, and cyclically, where `(a, b, c)` is the magnetic
induction, `(F, G, H)` the electromagnetic momentum (vector potential), and `Ψ` a function first
introduced "for the sake of giving generality". Maxwell is explicit that it is not yet fixed: "The
quantity Ψ is therefore indeterminate as far as regards the problem now before us. We shall find,
however, that when we know all the circumstances of the problem, we can assign a definite value to
Ψ, and that it represents, according to a certain definition, the electric potential at the point
x, y, z" (p. 221). `emf598` takes `∇Ψ` as an argument and does not choose it.
The vector `𝔈` is "the force which would be experienced by a unit of positive electricity placed
at that point" (p. 221).

Art. 599 (p. 222), quaternion form `𝔈 = V.𝔊𝔅 − 𝔄̇ − ∇Ψ`: the motional part "is the vector part of
the product of the magnetic induction, multiplied by the velocity, that is to say, the magnitude
of the electromotive force is represented by the area of the parallelogram, whose sides represent
the velocity and the magnetic induction, and its direction is the normal to this parallelogram,
drawn so that the velocity, the magnetic induction, and the electromotive force are in
right-handed cyclical order."

This is the electromotive *intensity* at a point of a moving body. It is not yet the later
Heaviside–Lorentz force law on a point charge `q(E + v × B)`; nothing here asserts that law.

Source: Internet Archive `electricandmagne02maxwrich` (1873, vol. II).
-/

namespace Maxwell

open Matrix

/-- **Art. 598, equations (B), p. 221**, in the vector form of Art. 599, eq. (10):
`𝔈 = 𝔊 × 𝔅 − 𝔄̇ − ∇Ψ`, with `𝔊` the velocity of the element, `𝔅` the induction, `𝔄̇` the time
derivative of the electromagnetic momentum, `∇Ψ` the gradient of `Ψ`. -/
def emf598 (velocity B dAdt gradΨ : Vec3) : Vec3 :=
  crossProduct velocity B - dAdt - gradΨ

/-- Equations (B) of Art. 598 as printed: `P = c ẏ − b ż − Ḟ − dΨ/dx`, etc. -/
theorem art598_components (v B dAdt gradΨ : Vec3) :
    emf598 v B dAdt gradΨ 0 = B 2 * v 1 - B 1 * v 2 - dAdt 0 - gradΨ 0 ∧
    emf598 v B dAdt gradΨ 1 = B 0 * v 2 - B 2 * v 0 - dAdt 1 - gradΨ 1 ∧
    emf598 v B dAdt gradΨ 2 = B 1 * v 0 - B 0 * v 1 - dAdt 2 - gradΨ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [emf598, cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- **Art. 599, eq. (7), p. 222.** The motional part `𝔈₁ = V.𝔊𝔅` is normal to the
parallelogram on the velocity and the induction, its square is the squared area
`|𝔊|²|𝔅|² − (𝔊·𝔅)²`, and velocity, induction and electromotive force are in right-handed
cyclical order (the determinate `det[𝔊, 𝔅, 𝔈₁] = |𝔈₁|² ≥ 0`). -/
theorem art599_motional (v B : Vec3) :
    v ⬝ᵥ crossProduct v B = 0 ∧ B ⬝ᵥ crossProduct v B = 0 ∧
    sq (crossProduct v B) = sq v * sq B - (v ⬝ᵥ B) ^ 2 ∧
    Matrix.det ![v, B, crossProduct v B] = sq (crossProduct v B) ∧
    0 ≤ Matrix.det ![v, B, crossProduct v B] := by
  have hdet : Matrix.det ![v, B, crossProduct v B] = sq (crossProduct v B) := by
    rw [← triple_product_eq_det, triple_product_permutation, triple_product_permutation, sq]
  refine ⟨dot_self_cross v B, dot_cross_self v B, ?_, hdet, hdet ▸ sq_nonneg' _⟩
  simp only [sq, cross_dot_cross]; rw [dotProduct_comm B v]; ring

/-! ## Art. 590: 𝔄 as the impulse of the electromotive force -/

open MeasureTheory in
/-- **Target.** Treatise 1873, vol. II, Art. 590, p. 214: 𝔄 "represents in direction and
magnitude the time-integral of the electromotive force which a particle placed at the point
`(x, y, z)` would experience if the primary current were suddenly stopped." For a body at rest
(`velocity = 0`) with `Ψ = 0`, `∫₀^∞ emf598 0 B (∂ₜ𝔄) 0 dt = 𝔄(0)` when `𝔄 → 0` as
`t → ∞`. This is Lagrangian / generalized momentum (Art. 604), not a field momentum density. Proved below as `art590_impulse`. -/
def Art590Impulse : Prop :=
  ∀ (A : ℝ → Vec3) (B : Vec3),
    (∀ t, DifferentiableAt ℝ A t) →
    Filter.Tendsto A Filter.atTop (nhds (0 : Vec3)) →
    IntegrableOn (fun t => emf598 0 B (deriv A t) 0) (Set.Ici (0 : ℝ)) →
      ∫ t in Set.Ici (0 : ℝ), emf598 0 B (deriv A t) 0 = A 0

open MeasureTheory in
/-- **Art. 590.** With `velocity = 0` and `Ψ = 0`, `emf598 = −∂ₜ𝔄`, and
`∫₀^∞ −𝔄′ = 𝔄(0) − lim 𝔄 = 𝔄(0)` (`integral_Ioi_of_hasDerivAt_of_tendsto'`). -/
theorem art590_impulse : Art590Impulse := by
  intro A B hA hlim hint
  have he : ∀ t, emf598 0 B (deriv A t) 0 = - deriv A t := fun t => by simp [emf598]
  simp_rw [he] at hint ⊢
  rw [integral_neg, integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => (hA t).hasDerivAt)
      (by simpa using hint.neg.mono_set Set.Ioi_subset_Ici_self) hlim]
  simp

end Maxwell
