/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.ElectrostaticStress

/-!
# Magnetic stress and the electromagnetic force (Treatise 1873, vol. II, Arts. 639–645)

Maxwell's order is followed exactly.

* **Arts. 639–640 (pp. 251–253).** The force and couple on a magnetized element carrying a
  current, from the old (Poisson) theory of magnetism: `X = A dα/dx + B dβ/dx + C dγ/dx + vc − wb`,
  `L = Bγ − Cβ`, with `(A, B, C)` the magnetization, `(α, β, γ)` the magnetic force `H`,
  `(a, b, c)` the induction `B = H + 4πI` (Art. 400), and `4πu = dγ/dy − dβ/dz`, … (Art. 607).
* **Art. 640 (p. 253) into Art. 641 (pp. 253–254).** A stress `P_hk` that reproduces this force
  and couple: `P_hk = (1/4π) B_h H_k − δ_hk H²/8π` (eq. (15)). The step `da/dx + db/dy + dc/dz = 0`
  (Art. 403, "the solenoidal condition which is always satisfied by the components of the
  magnetic induction", vol. II, p. 26) is used in Art. 640, eq. (8) at the top of p. 253, to turn
  eq. (7) into eq. (9), which Art. 641's stress then matches. "In the case of a magnetized body,
  however, there is such a tendency to rotation, and therefore this condition [`P_hk = P_kh`] …
  is not fulfilled."
* **Art. 642 (p. 255).** In axes bisecting `B` and `H`: a pressure `H²/8π` in all directions,
  a tension `(1/4π) BH cos²ε` along the bisector, a pressure `(1/4π) BH sin²ε` along the exterior
  bisector, and a couple `(1/4π) BH sin 2ε` turning each element from `B` toward `H`. The
  isotropic part is `H²/8π` (not the later Minkowski `B·H/8π`).
* **Art. 643 (pp. 256–257).** Unmagnetized (`B = H`): tension `H²/8π` along the lines of force
  with an equal lateral pressure; the force per unit volume is
  `X = αm + vγ − wβ`, `m` "the density of austral magnetic matter referred to unit of volume"
  (`dα/dx + dβ/dy + dγ/dz = 4πm`). The `m` term is kept as a formal object.
* **Art. 644 (p. 257).** *Separate hypothesis*: "If we adopt the theories of Ampere and Weber …
  we get rid of imaginary magnetic matter, and find that everywhere `m = 0`", giving
  `X = vγ − wβ` (eqs. (22) = equations (C) of Art. 603). It is a hypothesis (`AmpereWeber644`),
  never a default.
* **Art. 645 (pp. 257–258)** records the superposition of the electrostatic and electromagnetic
  stresses as a hypothesis (`stress645`, `art645_force`) and states a limit that is *not*
  formalized as anything proved: "We have asserted nothing as yet with respect to the mode in
  which this state of stress is originated and maintained in the medium. … it remains to be seen
  whether the conception of a medium capable of supporting these states of stress is consistent
  with other known phenomena, or whether we shall have to put it aside as unfruitful." See
  `Maxwell.Sources.art645`.

Fidelity note. Art. 640's reduction of (7) to (9), which Art. 641's stress matches, uses
`div B = 0` (Art. 403, eq. (8) on p. 253); Art. 643 then sets `B = H` and keeps `div H = 4πm`.
With `B = H`, Art. 403 would force `m = 0`. That last inference is ours, not Maxwell's: he
reaches `m = 0` by the Ampère–Weber hypothesis of Art. 644, not by combining Art. 403 with
`B = H`. The formalization therefore keeps the two routes apart: `art641_force` has Art. 403
as an explicit hypothesis; `art643_force` does not assume it. See `art643_m_eq_zero_of_art403`.

Source: Internet Archive `electricandmagne02maxwrich` (1873, vol. II).
-/

namespace Maxwell

open Matrix

/-- **Treatise 1873, vol. II, Art. 641, eq. (15), p. 254.** The magnetic stress, induction
`B = (a, b, c)`, magnetic force `H = (α, β, γ)`: `P_xx = (1/4π)(aα − ½(α² + β² + γ²))`,
`P_yz = (1/4π) bγ`, `P_zy = (1/4π) cβ`, and so on. Not symmetric in general. -/
noncomputable def magneticStress641 (B H : Vec3) : Stress :=
  fun h k => B h * H k / fourPi - δ h k * sq H / (8 * Real.pi)

/-- The printed components of Art. 641, eq. (15), p. 254. -/
theorem art641_components (B H : Vec3) :
    magneticStress641 B H 0 0 = (B 0 * H 0 - sq H / 2) / (4 * Real.pi) ∧
    magneticStress641 B H 1 2 = B 1 * H 2 / (4 * Real.pi) ∧
    magneticStress641 B H 2 1 = B 2 * H 1 / (4 * Real.pi) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [magneticStress641, δ, fourPi]
  field_simp; ring

/-- **Art. 641, eq. (14) and (11), p. 254:** the couple of the stress, `L = P_yz − P_zy`, is
`(1/4π)(bγ − cβ)`, i.e. `(1/4π) B × H`. -/
theorem art641_couple (B H : Vec3) :
    couple (magneticStress641 B H) = (1 / fourPi) • crossProduct B H := by
  ext i
  fin_cases i <;> simp [couple, magneticStress641, δ, cross_apply, fourPi] <;> ring

/-- **Art. 639, eq. (2), p. 252, with Art. 400 (`B = H + 4πI`):** the stress couple equals the
couple `L = Bγ − Cβ` on the magnetized element, i.e. `I × H`. -/
theorem art639_couple {B H I : Vec3} (hArt400 : B = H + fourPi • I) :
    couple (magneticStress641 B H) = crossProduct I H := by
  rw [art641_couple, hArt400]
  have : fourPi ≠ 0 := by simp [fourPi, Real.pi_ne_zero]
  ext i
  fin_cases i <;> simp [cross_apply] <;> field_simp

/-- **Art. 641, p. 253:** "In the case of a magnetized body … this condition [`P_hk = P_kh`] …
is not fulfilled." Exactly: the stress is symmetric iff `B × H = 0`, i.e. iff the induction is
along the magnetic force. -/
theorem art641_symm_iff (B H : Vec3) :
    (magneticStress641 B H)ᵀ = magneticStress641 B H ↔ crossProduct B H = 0 := by
  have hpi : (4 * Real.pi) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · intro h
    have e : ∀ a b, magneticStress641 B H a b = magneticStress641 B H b a := fun a b => by
      have := congrFun (congrFun h b) a; simpa using this
    have e12 := e 1 2; have e20 := e 2 0; have e01 := e 0 1
    simp [magneticStress641, δ, fourPi] at e12 e20 e01
    ext i
    fin_cases i <;> simp [cross_apply] <;> field_simp at e12 e20 e01 ⊢ <;> linarith
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
    simp [cross_apply] at h0 h1 h2
    ext a b
    fin_cases a <;> fin_cases b <;> simp [magneticStress641, δ] <;> field_simp <;> linarith

/-- **Art. 642, p. 255:** "When the magnetic induction is in the same direction as the magnetic
force, as it always is in fluids and non-magnetized solids … the tangential stresses
disappear." For `B = μ H` the stress is symmetric. -/
theorem art642_parallel (μ : ℝ) (H : Vec3) :
    (magneticStress641 (μ • H) H)ᵀ = magneticStress641 (μ • H) H := by
  rw [art641_symm_iff]; simp

/-- **Art. 642, last paragraph, pp. 255–256, eq. (18):** "When the magnetic induction is in the
same direction as the magnetic force, as it always is in fluids and non-magnetized solids …
the stress in this case is therefore a hydrostatic pressure `(1/8π) ℌ²`, combined with a
longitudinal tension `(1/4π) 𝔅ℌ` along the lines of force." His case is `ε = 0`, so `μ > 0`.
For `B = μ H` with `H = r û` and `û` a unit vector along `H` (`r` may be negative; only `r²`
enters), this is `−(H²/8π) · 1 + (μ H²/4π) û ûᵀ`. The algebra holds for any real `μ`, which
is more general than his. The components (18) are `P_xx = (1/4π)(𝔅ℌ − ½ ℌ²)`,
`P_yy = P_zz = −ℌ²/8π`. -/
theorem art642_along_H (μ r : ℝ) {u : Vec3} (hu : u ⬝ᵥ u = 1) :
    magneticStress641 (μ • (r • u)) (r • u) =
      (-((r ^ 2) / (8 * Real.pi))) • (1 : Stress) +
        (μ * (r ^ 2) / fourPi) • vecMulVec u u := by
  have hsq : sq (r • u) = r ^ 2 := by
    simp [sq, dotProduct_smul, smul_dotProduct, hu]; ring
  ext a b
  simp only [magneticStress641, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, vecMulVec,
    δ, fourPi, hsq, smul_eq_mul, Pi.smul_apply]
  by_cases hab : a = b
  · subst hab
    simp
    field_simp
    ring
  · simp [hab]
    ring

/-- **Art. 642, eq. (17), p. 255: the bisector decomposition.** Take the `x` axis bisecting
the angle `2ε` between `B` (numerical value `𝔅`) and `H` (numerical value `ℌ`), the `y` axis in
their plane toward `H`, so `a = 𝔅 cos ε`, `b = −𝔅 sin ε`, `α = ℌ cos ε`, `β = ℌ sin ε`. Then the
stress is
(1) a pressure `ℌ²/8π` equal in all directions,
(2) a tension `(1/4π) 𝔅ℌ cos²ε` along the bisector,
(3) a pressure `(1/4π) 𝔅ℌ sin²ε` along the exterior bisector, and
(4) an antisymmetric part `(1/4π) 𝔅ℌ cos ε sin ε (e_x e_yᵀ − e_y e_xᵀ)`, whose couple about
`z` is `(1/4π) 𝔅ℌ sin 2ε`, "tending to turn every element of the substance in the plane of the
two directions from the direction of magnetic induction to the direction of magnetic force." -/
theorem art642_bisector (𝔅 ℌ ε : ℝ) :
    let B : Vec3 := ![𝔅 * Real.cos ε, -(𝔅 * Real.sin ε), 0]
    let H : Vec3 := ![ℌ * Real.cos ε, ℌ * Real.sin ε, 0]
    magneticStress641 B H =
        (-(ℌ ^ 2 / (8 * Real.pi))) • (1 : Stress)
        + (𝔅 * ℌ * Real.cos ε ^ 2 / (4 * Real.pi)) • vecMulVec (axis 0) (axis 0)
        - (𝔅 * ℌ * Real.sin ε ^ 2 / (4 * Real.pi)) • vecMulVec (axis 1) (axis 1)
        + (𝔅 * ℌ * Real.cos ε * Real.sin ε / (4 * Real.pi)) •
            (vecMulVec (axis 0) (axis 1) - vecMulVec (axis 1) (axis 0)) ∧
    couple (magneticStress641 B H) 2 = 𝔅 * ℌ * Real.sin (2 * ε) / (4 * Real.pi) := by
  intro B H
  have hsq : sq H = ℌ ^ 2 := by
    have := Real.sin_sq_add_cos_sq ε
    simp [H, sq_eq]; linear_combination ℌ ^ 2 * this
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [magneticStress641, hsq, δ, B, H, axis, vecMulVec, fourPi] <;>
      field_simp <;> ring
  · simp [couple, magneticStress641, δ, B, H, Real.sin_two_mul, fourPi]
    field_simp; ring

/-- **Art. 643, p. 256:** "When there is no magnetization, `𝔅 = ℌ`, and the stress is still
further simplified, being a tension along the lines of force equal to `ℌ²/8π`, combined with a
pressure in all directions at right angles to the lines of force, numerically equal also to
`ℌ²/8π`." The unmagnetized stress has the same form as the electrostatic one. -/
theorem art643_unmagnetized (H : Vec3) : magneticStress641 H H = componentForm H := rfl

theorem art643_tension_pressure {H n : Vec3} (hn : H ⬝ᵥ n = 0) :
    traction (magneticStress641 H H) H = (sq H / (8 * Real.pi)) • H ∧
    traction (magneticStress641 H H) n = -(sq H / (8 * Real.pi)) • n :=
  ⟨art106_tension H, art106_pressure hn⟩

/-- **Art. 643, pp. 256–257, eq. (20): the equations of electromagnetic force with the
magnetic-matter term.** If `dα/dx + dβ/dy + dγ/dz = 4πm` (`m` the density of austral magnetic
matter) and `4π(u, v, w) = curl H` (Art. 607), the stress (19) (p. 256) gives
`X = αm + vγ − wβ`, `Y = βm + wα − uγ`, `Z = γm + uβ − vα`, i.e. `m H + J × H`.
No `div = 0` condition is assumed. Confirmed against the 1873 vol. II page scan, p. 257
(Internet Archive `electricandmagne02maxwrich`): the force-component display is labeled
"(Equations of Electromagnetic Force.) (20)". Art. 644 then prints
`dα/dx + dβ/dy + dγ/dz = 0` as (21), and the reduced force `X = vγ − wβ` &c. as (22). -/
theorem art643_force {H : Vec3 → Vec3} {x : Vec3} {m : ℝ} {J : Vec3}
    (hH : ∀ i, DifferentiableAt ℝ (fun y => H y i) x)
    (hm : div H x = fourPi * m) (hJ : curl H x = fourPi • J) :
    stressForce (fun y => magneticStress641 (H y) (H y)) x = m • H x + crossProduct J (H x) := by
  have h := stressForce_componentForm hH
  simp only [art643_unmagnetized]
  rw [h, hm, hJ]
  have : fourPi ≠ 0 := by simp [fourPi, Real.pi_ne_zero]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_smul, LinearMap.smul_apply]
  field_simp

/-- Art. 643, eq. (20), p. 257, component by component, as printed:
`X = αm + vγ − wβ`, `Y = βm + wα − uγ`, `Z = γm + uβ − vα`. -/
theorem art643_force_components {H : Vec3 → Vec3} {x : Vec3} {m : ℝ} {J : Vec3}
    (hH : ∀ i, DifferentiableAt ℝ (fun y => H y i) x)
    (hm : div H x = fourPi * m) (hJ : curl H x = fourPi • J) :
    let F := stressForce (fun y => magneticStress641 (H y) (H y)) x
    F 0 = H x 0 * m + J 1 * H x 2 - J 2 * H x 1 ∧
    F 1 = H x 1 * m + J 2 * H x 0 - J 0 * H x 2 ∧
    F 2 = H x 2 * m + J 0 * H x 1 - J 1 * H x 0 := by
  intro F
  have e := art643_force hH hm hJ
  refine ⟨?_, ?_, ?_⟩ <;> simp only [F, e] <;> simp [cross_apply] <;> ring

/-- **Art. 644, p. 257: the Ampère–Weber hypothesis, as a hypothesis.** "If we adopt the
theories of Ampere and Weber as to the nature of magnetic and diamagnetic bodies, and assume that
magnetic and diamagnetic polarity are due to molecular electric currents, we get rid of imaginary
magnetic matter, and find that everywhere `m = 0`," and, as eq. (21),
`dα/dx + dβ/dy + dγ/dz = 0`. -/
def AmpereWeber644 (m : Vec3 → ℝ) : Prop := ∀ x, m x = 0

/-- **Art. 644, eq. (22), p. 257:** under the Ampère–Weber hypothesis the equations of
electromagnetic force become `X = vγ − wβ`, `Y = wα − uγ`, `Z = uβ − vα` — "identical with those
already established (Equations (C), Art. 603)." -/
theorem art644_force {H : Vec3 → Vec3} {x : Vec3} {m : Vec3 → ℝ} {J : Vec3}
    (hH : ∀ i, DifferentiableAt ℝ (fun y => H y i) x)
    (hm : div H x = fourPi * m x) (hJ : curl H x = fourPi • J) (hAW : AmpereWeber644 m) :
    stressForce (fun y => magneticStress641 (H y) (H y)) x = crossProduct J (H x) := by
  rw [art643_force hH hm hJ, hAW x, zero_smul, zero_add]

/-- **Our observation, not Maxwell's route.** If one combines Art. 643's unmagnetized case
`B = H` with Art. 403 / Art. 640 eq. (8) (`div B = 0`) and Art. 643's `div H = 4πm`, then
`m = 0` (with `B = H` as fields, as in Art. 643, not only at one point). Maxwell does not take
this path: he reaches `m = 0` by the Ampère–Weber hypothesis of
Art. 644 ("we get rid of imaginary magnetic matter, and find that everywhere `m = 0`"). -/
theorem art643_m_eq_zero_of_art403 {B H : Vec3 → Vec3} {x : Vec3} {m : ℝ}
    (hBH : B = H) (hArt403 : div B x = 0) (hm : div H x = fourPi * m) : m = 0 := by
  subst hBH
  have : fourPi * m = 0 := by rw [← hm, hArt403]
  have hpi : fourPi ≠ 0 := by simp [fourPi, Real.pi_ne_zero]
  exact (mul_eq_zero.mp this).resolve_left hpi

/-- The force of a sum of stresses is the sum of the forces (entrywise differentiable). -/
theorem stressForce_add {P Q : Vec3 → Stress} {x : Vec3}
    (hP : ∀ h k, DifferentiableAt ℝ (fun y => P y h k) x)
    (hQ : ∀ h k, DifferentiableAt ℝ (fun y => Q y h k) x) :
    stressForce (fun y => P y + Q y) x = stressForce P x + stressForce Q x := by
  ext k
  simp only [stressForce, Matrix.add_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun h _ => pd_add h (hP h k) (hQ h k)

theorem differentiableAt_magneticStress641 {B H : Vec3 → Vec3} {x : Vec3}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (hH : ∀ i, DifferentiableAt ℝ (fun y => H y i) x) (h k : Fin 3) :
    DifferentiableAt ℝ (fun y => magneticStress641 (B y) (H y) h k) x := by
  simp only [magneticStress641, sq_eq]
  have := hH 0; have := hH 1; have := hH 2; have := hB h; have := hH k
  fun_prop

/-! ## Art. 645: superposition of the two stresses, as his hypothesis -/

/-- **Art. 645, p. 258, hypothesis:** "In a field in which electrostatic as well as
electromagnetic action is taking place, we must suppose the electrostatic stress described in
Part I to be superposed on the electromagnetic stress which we have been considering."
(`Maxwell.Sources.art645_superposition`.) -/
noncomputable def stress645 (E B H : Vec3) : Stress :=
  componentForm E + magneticStress641 B H

/-- **Art. 645, hypothesis**, using Art. 108 (electric, no curl, Art. 77) and Art. 643
(unmagnetized magnetic, `B = H`, `div H = 4πm`, `4πJ = curl H`): the superposed stress produces
the force `ρ E + m H + J × H` per unit volume. Tagged as his hypothesis because the
superposition itself is ("we must suppose … superposed"). The electrostatic half uses
`componentForm E` as in 1873 Art. 108; 1881 Art. 105 writes the same matrix from `E = −∇Ψ`. -/
theorem art645_force {E H : Vec3 → Vec3} {x : Vec3} {ρ m : ℝ} {J : Vec3}
    (hE : ∀ i, DifferentiableAt ℝ (fun y => E y i) x)
    (hH : ∀ i, DifferentiableAt ℝ (fun y => H y i) x)
    (hcurlE : curl E x = 0) (hArt77 : div E x = fourPi * ρ)
    (hm : div H x = fourPi * m) (hJ : curl H x = fourPi • J) :
    stressForce (fun y => stress645 (E y) (H y) (H y)) x =
      ρ • E x + m • H x + crossProduct J (H x) := by
  have hadd : (fun y => stress645 (E y) (H y) (H y)) =
      fun y => componentForm (E y) + magneticStress641 (H y) (H y) := rfl
  rw [hadd, stressForce_add (differentiableAt_componentForm hE)
    (differentiableAt_magneticStress641 hH hH), art108_force hE hcurlE hArt77,
    art643_force hH hm hJ, add_assoc]

/-! ## Arts. 639–641: the magnetized case -/

theorem pd_magneticStress641 {B H : Vec3 → Vec3} {x : Vec3}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (hH : ∀ i, DifferentiableAt ℝ (fun y => H y i) x) (h k : Fin 3) :
    pd h (fun y => magneticStress641 (B y) (H y) h k) x =
      (pd h (fun y => B y h) x * H x k + B x h * pd h (fun y => H y k) x) / fourPi
      - δ h k * (2 * (H x 0 * pd h (fun y => H y 0) x + H x 1 * pd h (fun y => H y 1) x
          + H x 2 * pd h (fun y => H y 2) x)) / (8 * Real.pi) := by
  have e : (fun y => magneticStress641 (B y) (H y) h k) = fun y =>
      (1 / fourPi) * (B y h * H y k) - (δ h k / (8 * Real.pi)) *
        (H y 0 * H y 0 + H y 1 * H y 1 + H y 2 * H y 2) := by
    funext y; simp only [magneticStress641, sq_eq]; ring
  have h0 := hH 0; have h1 := hH 1; have h2 := hH 2; have hh := hB h; have hk := hH k
  rw [e, pd_sub _ (by fun_prop) (by fun_prop), pd_const_mul _ _ (by fun_prop),
    pd_const_mul _ _ (by fun_prop), pd_mul _ hh hk, pd_add _ (by fun_prop) (by fun_prop),
    pd_add _ (by fun_prop) (by fun_prop), pd_mul _ h0 h0, pd_mul _ h1 h1, pd_mul _ h2 h2]
  ring

/-- **Arts. 639–641, eqs. (4), (7)–(9), (13), (15), pp. 252–254.** In a magnetized body carrying
a current, with `B = H + 4πI` at the point (Art. 400), `4πJ = curl H` (Art. 607) and Maxwell's
own use of `da/dx + db/dy + dc/dz = 0` (Art. 403, used in Art. 640 as eq. (8) on p. 253 to
reduce (7) to (9), which Art. 641's stress matches), the force of the stress (15)
equals the force (4) on the element:
`X = A dα/dx + B dβ/dx + C dγ/dx + vc − wb`, i.e. `∑ᵢ Iᵢ ∂ₖHᵢ + (J × B)ₖ`. Together with
`art639_couple` this is Maxwell's statement that the stress is "statically equivalent, in its
effects on each element of the body, with the forces arising from the magnetization and electric
currents" (p. 255). -/
theorem art641_force {B H : Vec3 → Vec3} {x : Vec3} {I J : Vec3}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (hH : ∀ i, DifferentiableAt ℝ (fun y => H y i) x)
    (hArt400 : B x = H x + fourPi • I) (hArt607 : curl H x = fourPi • J)
    (hArt403 : div B x = 0) :
    stressForce (fun y => magneticStress641 (B y) (H y)) x =
      (fun k => ∑ i, I i * pd k (fun y => H y i) x) + crossProduct J (B x) := by
  have hpi : fourPi ≠ 0 := by simp [fourPi, Real.pi_ne_zero]
  have hI : I = (1 / fourPi) • (B x - H x) := by
    rw [hArt400]; ext i; simp; field_simp
  have hJ : J = (1 / fourPi) • curl H x := by
    rw [hArt607]; ext i; simp; field_simp
  rw [hI, hJ]
  simp only [div, Fin.sum_univ_three] at hArt403
  ext k
  simp only [stressForce, pd_magneticStress641 hB hH, Fin.sum_univ_three, curl, cross_apply,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, δ, map_smul, LinearMap.smul_apply]
  fin_cases k <;> simp [fourPi] <;> field_simp <;> linear_combination (8 * H x _) * hArt403
end Maxwell
