/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.Energy

/-!
# Pressure of radiation, from the stresses (Treatise 1873, vol. II, Art. 792)

Art. 792 (p. 391): in a plane wave the electric and magnetic disturbances lie in the plane of
the wave (Art. 791). "In virtue of the electrostatic state of the medium, there is a tension
whose magnitude is `p`, in a direction parallel to `x`, combined with a pressure, also equal to
`p`, parallel to `y` and `z`. See Art. 107. In virtue of the electrokinetic state of the medium
there is a tension equal to `p` in a direction parallel to `y`, combined with a pressure equal
to `p` in directions parallel to `x` and `z`. See Art. 643. Hence the combined effect … is a
pressure equal to `2p` in the direction of the propagation of the wave. Now `2p` also expresses
the whole energy in unit of volume. Hence in a medium in which waves are propagated there is a
pressure in the direction normal to the waves, and numerically equal to the energy in unit of
volume."

This is derived **from the stresses** (Arts. 107 and 643, superposed as Art. 645 directs). It is
not derived from a momentum density of the field, which Maxwell does not have (that reading is
later: J. J. Thomson 1891, Heaviside, Poincaré 1900, Abraham 1903). No energy-flux vector
appears either.

Two sharpenings, both proved below:
* the equality of the two halves (eq. (8), p. 391) is not needed: the normal pressure equals the
  *sum* of the two energies whenever both disturbances are transverse;
* Art. 792 cites Art. 643, which is the *unmagnetized* case `B = H`. If one instead takes the
  magnetized stress of Arts. 641–642 literally with `B = μH`, the magnetic contribution to the
  normal pressure is `H²/8π`, which equals the electrokinetic energy `μH²/8π` only when `μ = 1`.

Local source: `/workspace/maxwell_reread/n_electricandmagne02maxwrich.txt`.
-/

namespace Maxwell

open Matrix

/-- Normal stress across a plane with unit normal `n`: positive is a tension, negative a
pressure (Art. 108). -/
def normalStress (P : Stress) (n : Vec3) : ℝ := n ⬝ᵥ traction P n

theorem normalStress_tensionWithLateralPressure (p : ℝ) {u n : Vec3} (hn : n ⬝ᵥ n = 1)
    (hun : u ⬝ᵥ n = 0) : normalStress (tensionWithLateralPressure p u) n = -p := by
  have e : normalStress (tensionWithLateralPressure p u) n =
      p * (2 * (u ⬝ᵥ n) ^ 2 - n ⬝ᵥ n) := by
    simp only [normalStress, traction, tensionWithLateralPressure, dotProduct, Fin.sum_univ_three,
      δ]
    simp; ring
  rw [e, hun, hn]; ring

theorem normalStress_add (P Q : Stress) (n : Vec3) :
    normalStress (P + Q) n = normalStress P n + normalStress Q n := by
  simp only [normalStress, traction, Matrix.add_apply, dotProduct, Fin.sum_univ_three]; ring

/-- **Art. 792, p. 391, as Maxwell argues it.** In a medium of capacity `K` and permeability
`μ`, with the electric disturbance `E` and magnetic disturbance `H` in the plane of the wave
(normal `n`), take with Art. 792 a tension `p₁ = K E²/8π` along `E` with equal lateral pressure
(Art. 107) and a tension `p₂ = μ H²/8π` along `H` with equal lateral pressure (Art. 643). The
superposed stress (Art. 645) is a pressure across the wave-front equal to the whole energy in
unit of volume, `electrostaticEnergy631 + electrokineticEnergy636`.
The equality `p₁ = p₂` of eq. (8) is not used. `uE`, `uH` stand for the directions of `E`, `H`;
only their transversality `uE ⊥ n`, `uH ⊥ n` (Art. 791) is used. -/
theorem art792_radiation_pressure (K μ : ℝ) {E H uE uH n : Vec3} (hn : n ⬝ᵥ n = 1) (hEn : uE ⬝ᵥ n = 0) (hHn : uH ⬝ᵥ n = 0) :
    normalStress (tensionWithLateralPressure (K * sq E / (8 * Real.pi)) uE +
        tensionWithLateralPressure (μ * sq H / (8 * Real.pi)) uH) n =
      -(electrostaticEnergy631 E ((K / fourPi) • E) + electrokineticEnergy636 (μ • H) H) := by
  rw [normalStress_add, normalStress_tensionWithLateralPressure _ hn hEn,
    normalStress_tensionWithLateralPressure _ hn hHn, (energy_isotropic K μ E H).1,
    (energy_isotropic K μ E H).2]
  ring

/-- **Art. 792 with the stresses of Arts. 108 and 643 in their own component form** (`K = μ = 1`,
the case those articles treat): for a transverse disturbance, the superposed stress
`componentForm E + magneticStress641 H H` gives a pressure across the wave-front equal to
`E²/8π + H²/8π`, the whole energy in unit of volume. -/
theorem art792_radiation_pressure_components {E H n : Vec3} (hn : n ⬝ᵥ n = 1)
    (hEn : E ⬝ᵥ n = 0) (hHn : H ⬝ᵥ n = 0) :
    normalStress (componentForm E + magneticStress641 H H) n =
      -(electrostaticEnergy631 E ((1 / fourPi) • E) + electrokineticEnergy636 H H) := by
  rw [normalStress_add, art643_unmagnetized]
  have key : ∀ v : Vec3, v ⬝ᵥ n = 0 → normalStress (componentForm v) n = -(sq v / (8 * Real.pi)) :=
    by
    intro v hv
    simp only [normalStress, art106_pressure hv]
    simp [dotProduct_smul, hn]
  rw [key E hEn, key H hHn]
  simp [electrostaticEnergy631, electrokineticEnergy636, sq, dotProduct_smul, fourPi]
  field_simp; ring

/-- **Sharpening of Art. 792 against Arts. 641–642.** With the magnetized stress taken literally
for `B = μH` and `H` in the wave-front, the magnetic part of the normal stress across the front is
the isotropic pressure `H²/8π` of Art. 642 (1), independent of `μ`. -/
theorem art642_normalStress_transverse (μ : ℝ) {H n : Vec3} (hn : n ⬝ᵥ n = 1)
    (hHn : H ⬝ᵥ n = 0) :
    normalStress (magneticStress641 (μ • H) H) n = -(sq H / (8 * Real.pi)) := by
  have e : normalStress (magneticStress641 (μ • H) H) n =
      μ * (H ⬝ᵥ n) ^ 2 / fourPi - sq H / (8 * Real.pi) * (n ⬝ᵥ n) := by
    simp only [normalStress, traction, magneticStress641, dotProduct, Fin.sum_univ_three, δ]
    simp; ring
  rw [e, hHn, hn]; ring

/-- Consequently the magnetic contribution equals the electrokinetic energy `μH²/8π` of
Art. 792 eq. (23) only if `μ = 1` (or `H = 0`). -/
theorem art642_vs_art792 (μ : ℝ) {H n : Vec3} (hn : n ⬝ᵥ n = 1) (hHn : H ⬝ᵥ n = 0) :
    normalStress (magneticStress641 (μ • H) H) n = -electrokineticEnergy636 (μ • H) H ↔
      (μ = 1 ∨ sq H = 0) := by
  rw [art642_normalStress_transverse μ hn hHn, (energy_isotropic 1 μ H H).2]
  have hpi : (8 * Real.pi) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · intro h
    have : (μ - 1) * sq H = 0 := by field_simp at h; linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; exact h1
  · rintro (h | h)
    · subst h; ring
    · rw [h]; ring

end Maxwell
