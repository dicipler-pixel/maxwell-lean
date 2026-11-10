/-
Copyright (c) 2026. Released under the MIT license (see LICENSE).

# Adversarial audit of the load-bearing stress/energy theorems

Audits `art108_force`, `art105_force`, `art111_energy_eq_tension`, `art641_force`,
`art642_bisector`/`art642_along_H`, `art643_force`, `art792_radiation_pressure`.

The file is deliberately *not* part of the library: every theorem here is either a model that
shows a hypothesis is met and the conclusion non-vacuous (`*_model`, `*_nonvacuous`), a
counterexample showing a hypothesis is load-bearing (`*_needs_*`), a numeric evaluation of a
formula as printed in the Treatise, or a repaired/strengthened statement where the audit found a
gap (`dielectricStress`, `stressForce_dielectricStress`, `art792_with_field_stress`).

Nothing here changes an existing statement: the audited theorem names are only *used*.
-/
import Maxwell.Treatise.RadiationPressure

namespace Maxwell

open Matrix

/-! ## 0. Calculus helpers for the audit models

`pd_axis_apply` and `pd_sq` are the only derivatives the models need; they are not in the
library. -/

/-- The partial derivative of a coordinate function is the Kronecker delta. -/
theorem pd_axis_apply (i j : Fin 3) (x : Vec3) : pd i (fun y : Vec3 => y j) x = δ i j := by
  unfold pd
  rw [(hasFDerivAt_apply j x).fderiv]
  simp only [ContinuousLinearMap.proj_apply, axis, δ]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem differentiableAt_sq (x : Vec3) : DifferentiableAt ℝ (fun y : Vec3 => sq y) x := by
  have e : (fun y : Vec3 => sq y) = fun y => y 0 * y 0 + y 1 * y 1 + y 2 * y 2 := by
    funext y; simp [sq_eq, pow_two]
  rw [e]; fun_prop

/-- `∂ᵢ (X² + Y² + Z²) = 2 xᵢ`. -/
theorem pd_sq (i : Fin 3) (x : Vec3) : pd i (fun y : Vec3 => sq y) x = 2 * x i := by
  have e : (fun y : Vec3 => sq y) = fun y => y 0 * y 0 + y 1 * y 1 + y 2 * y 2 := by
    funext y; simp [sq_eq, pow_two]
  rw [e, pd_add _ (by fun_prop) (by fun_prop), pd_add _ (by fun_prop) (by fun_prop),
    pd_mul _ (by fun_prop) (by fun_prop), pd_mul _ (by fun_prop) (by fun_prop),
    pd_mul _ (by fun_prop) (by fun_prop)]
  simp only [pd_axis_apply, δ]
  fin_cases i <;> simp <;> ring

/-! ## 1. The stress force of the identity field `x ↦ x`

This is the single computation behind all the models below: for `F = id` the stress
`componentForm x` has `stressForce = (3/4π) • x`, because `div id = 3` and `curl id = 0`. -/

theorem idField_div (x : Vec3) : div (fun y : Vec3 => y) x = 3 := by
  simp only [div, pd_axis_apply, Fin.sum_univ_three, δ]
  norm_num

theorem idField_curl (x : Vec3) : curl (fun y : Vec3 => y) x = 0 := by
  ext i
  fin_cases i <;> simp [curl, pd_axis_apply, δ]

theorem idField_diff (x : Vec3) : ∀ i, DifferentiableAt ℝ (fun y : Vec3 => y i) x :=
  fun i => (hasFDerivAt_apply i x).differentiableAt

/-- **The model computation.** `stressForce (componentForm ∘ id) = (3/4π) • x`. -/
theorem stressForce_componentForm_id (x : Vec3) :
    stressForce (fun y : Vec3 => componentForm y) x = (3 / fourPi) • x := by
  have hF : ∀ i, DifferentiableAt ℝ (fun y : Vec3 => y i) x := idField_diff x
  ext k
  simp only [stressForce, pd_componentForm hF, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul,
    pd_axis_apply, δ]
  fin_cases k <;> simp <;> field_simp <;> ring

/-! ## 2. Non-vacuity of `art108_force` (1873 Art. 108 eqs. (7)–(10))

The hypotheses `curl R = 0` and `div R = 4πρ` are met at `R = id` with `ρ = 3/4π`, and the
conclusion is then the *nonzero* field `(3/4π) • x`, independently computed in §1. -/

/-- `art108_force` at `R = id`, `ρ = 3/4π`. -/
theorem art108_force_at_id (x : Vec3) :
    stressForce (fun y : Vec3 => componentForm y) x = (3 / fourPi) • x :=
  art108_force (R := fun y : Vec3 => y) (x := x) (ρ := 3 / fourPi) (idField_diff x) (idField_curl x)
    (by rw [idField_div]; field_simp)

/-- The instance is non-vacuous: the force is `3/4π ≠ 0` along the first axis. -/
theorem art108_force_nonvacuous :
    (stressForce (fun y : Vec3 => componentForm y) ![1, 0, 0]) 0 = 3 / fourPi ∧
      (3 / fourPi : ℝ) ≠ 0 := by
  refine ⟨?_, by positivity⟩
  rw [art108_force_at_id]
  simp [Pi.smul_apply, smul_eq_mul]

/-! ## 3. Non-vacuity of `art105_force` (1881 Arts. 103–105)

`Ψ = −½|x|²` has `∇²Ψ = 3` in Maxwell's sign, so `ρ = 3/4π`; the stress of `Ψ` is
`componentForm (∇Ψ) = componentForm (−x) = componentForm x`, so the force is again
`(3/4π) • x`. This checks the Poisson hypothesis is satisfiable with `ρ ≠ 0`. -/

theorem contDiff_quadratic : ContDiff ℝ 2 (fun y : Vec3 => -(sq y) / 2) := by
  have e : (fun y : Vec3 => -(sq y) / 2)
      = fun y => (-(1 / 2)) * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
    funext y; rw [sq_eq]; ring
  rw [e]; fun_prop

theorem pd_neg_half_sq (i : Fin 3) (x : Vec3) :
    pd i (fun y : Vec3 => -(sq y) / 2) x = -x i := by
  have e : (fun y : Vec3 => -(sq y) / 2) = fun y => (-(1 / 2)) * sq y := by
    funext y; ring
  rw [e, pd_const_mul _ _ (differentiableAt_sq x), pd_sq]; ring

/-- `∇²Ψ = 3` for `Ψ = −½|x|²`, Maxwell's sign. -/
theorem maxwellNabla2_neg_half_sq (x : Vec3) :
    maxwellNabla2 (fun y : Vec3 => -(sq y) / 2) x = 3 := by
  have h : ∀ i : Fin 3, pd i (fun y : Vec3 => -y i) x = -1 := by
    intro i
    rw [pd_neg, pd_axis_apply]
    simp [δ]
  simp only [maxwellNabla2, pd_neg_half_sq, h, Fin.sum_univ_three]
  norm_num

theorem grad_neg_half_sq (x : Vec3) : grad (fun y : Vec3 => -(sq y) / 2) x = -x := by
  ext i
  simp only [grad, pd_neg_half_sq, Pi.neg_apply]

theorem componentForm_neg (v : Vec3) : componentForm (-v) = componentForm v := by
  ext h k
  simp only [componentForm, Pi.neg_apply, sq, dotProduct]
  have : ∑ i, -v i * -v i = ∑ i, v i * v i := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [this]; ring

/-- `art105_force` at `Ψ = −½|x|²`: hypotheses met with `ρ = 3/4π`, force `(3/4π) • x ≠ 0`. -/
theorem art105_force_at_quadratic (x : Vec3) :
    stressForce (fun y : Vec3 => stress1881 (fun z : Vec3 => -(sq z) / 2) y) x
      = (3 / fourPi) • x := by
  have hP : maxwellNabla2 (fun z : Vec3 => -(sq z) / 2) x = fourPi * (3 / fourPi) := by
    rw [maxwellNabla2_neg_half_sq]; field_simp
  have h := art105_force (Ψ := fun z : Vec3 => -(sq z) / 2) (x := x) (ρ := 3 / fourPi)
    (contDiff_quadratic.contDiffAt) hP
  rw [h, grad_neg_half_sq]
  simp


/-! ## 4. Non-vacuity of `art643_force` (1873 Art. 643 eq. (20), unmagnetized)

`H = id` gives `div H = 3` (so `m = 3/4π`) and `curl H = 0` (so `J = 0`); the conclusion is the
nonzero `(3/4π) • x`, matching §1 since `magneticStress641 H H = componentForm H`. -/

theorem art643_force_at_id (x : Vec3) :
    stressForce (fun y : Vec3 => magneticStress641 y y) x = (3 / fourPi) • x := by
  have h := art643_force (H := fun y : Vec3 => y) (x := x) (m := 3 / fourPi) (J := 0)
    (idField_diff x) (by rw [idField_div]; field_simp) (by rw [idField_curl]; simp)
  rw [h]
  simp

/-- The instance is non-vacuous: `(3/4π) • x ≠ 0`. -/
theorem art643_force_nonvacuous :
    (stressForce (fun y : Vec3 => magneticStress641 y y) ![1, 0, 0]) 0 = 3 / fourPi ∧
      (3 / fourPi : ℝ) ≠ 0 := by
  refine ⟨?_, by positivity⟩
  rw [art643_force_at_id]
  simp [Pi.smul_apply, smul_eq_mul]

/-- `∑ᵢ (c xᵢ) ∂ₖ xᵢ = c xₖ`: the `I·∇H` term for `H = id`, `I = c x`. -/
theorem sum_const_mul_pd (x : Vec3) (c : ℝ) (k : Fin 3) :
    ∑ i, (c * x i) * pd k (fun y : Vec3 => y i) x = c * x k := by
  simp only [pd_axis_apply, δ, Fin.sum_univ_three]
  fin_cases k <;> simp <;> ring

/-! ## 5. Non-vacuity of `art641_force` (Arts. 639–641): the magnetized case `I ≠ 0`

`B = 0`, `H = id`, `I = −H/4π`, `J = 0`. Then `B = H + 4πI`, `curl H = 4πJ`, `div B = 0`, and
`magneticStress641 0 H = −δ H²/8π` has stress force `−(1/4π) • x`, i.e. `I·∇H` — nonzero. So the
theorem is not vacuous in the magnetized case, and `I = 0` is not forced. -/

theorem art641_force_magnetized_model (x : Vec3) :
    stressForce (fun y : Vec3 => magneticStress641 0 y) x = (-(1 / fourPi)) • x := by
  have hB : ∀ i, DifferentiableAt ℝ (fun y : Vec3 => (0 : Vec3 → Vec3) y i) x := by
    intro i; exact differentiableAt_const (0 : ℝ)
  have h400 : (0 : Vec3) = (fun y : Vec3 => y) x + fourPi • (fun i => -(1 / fourPi) * x i) := by
    have hpi : fourPi ≠ 0 := by simp [fourPi, Real.pi_ne_zero]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    field_simp
    ring
  have h403 : div (fun _ : Vec3 => (0 : Vec3)) x = 0 := by
    simp [div, pd_const]
  have h607 : curl (fun y : Vec3 => y) x = fourPi • (0 : Vec3) := by
    rw [idField_curl]; simp
  have h := art641_force (B := fun _ : Vec3 => 0) (H := fun y : Vec3 => y)
    (I := fun i => -(1 / fourPi) * x i) (J := 0) (x := x) hB (idField_diff x) h400 h607 h403
  rw [h]
  ext k
  simp only [Pi.add_apply, sum_const_mul_pd, cross_apply, Pi.zero_apply, zero_mul,
    zero_add, Pi.smul_apply, smul_eq_mul]
  fin_cases k <;> simp

/-- **Art. 403 (`div B = 0`) is load-bearing for `art641_force`.** With `B = H = x`,
`I = J = 0` every hypothesis of `art641_force` *except* `div B = 0` holds (`div B = 3`), and the
conclusion fails: the stress force is `(3/4π) • x ≠ 0`, while the right-hand side
`∑ᵢ Iᵢ ∂ₖHᵢ + (J × B)ₖ` of `art641_force` is the zero vector field (both terms carry `I = 0` or
`J = 0`). So the
hypothesis cannot be dropped, and the theorem is exactly as strong as Maxwell's use of Art. 403
in Art. 640 eq. (8). -/
theorem art641_force_needs_art403 :
    stressForce (fun y : Vec3 => magneticStress641 y y) ![1, 0, 0] ≠ 0 := by
  intro h
  have e : (fun y : Vec3 => magneticStress641 y y) = fun y => componentForm y := by
    funext y; exact art643_unmagnetized y
  rw [e, stressForce_componentForm_id] at h
  have h0 := congrFun h 0
  simp only [Pi.smul_apply, smul_eq_mul] at h0
  have hne : (3 / fourPi : ℝ) ≠ 0 := by
    have := Real.pi_pos; simp only [fourPi]; positivity
  exact hne (by simpa using h0)

/-! ## 6. `art111_energy_eq_tension`: `K ≠ 0` is not needed

The printed identity holds in Lean's total division for `K = 0` as well (both sides are `0`),
so the hypothesis `hK : K ≠ 0` is redundant. -/

theorem art111_energy_eq_tension_all (K : ℝ) (R : Vec3) :
    (1 / 2) * (((K / fourPi) • R) ⬝ᵥ R) = K * sq R / (8 * Real.pi) ∧
    (1 / 2) * (((K / fourPi) • R) ⬝ᵥ R) = (2 * Real.pi / K) * sq ((K / fourPi) • R) := by
  rcases eq_or_ne K 0 with hK | hK
  · subst hK; simp
  · exact art111_energy_eq_tension K hK R


/-! ## 7. Art. 111 in a dielectric: the gap, and its repair

`art111_energy_eq_tension` proves the *numbers* `p = ½𝔇𝔈 = K 𝔈²/8π = (2π/K) 𝔇²`, but the
library attaches `p` to an actual stress matrix only for `K = 1` (`componentForm E`, whose tension
is `E²/8π`; see `art107_tension_of_art111`, `art106_tension`). For `K ≠ 1` no stress in the library
has tension `K E²/8π`: `componentForm E` gives `E²/8π`. The repair is `dielectricStress` below: its
tension along `E` is exactly `½𝔇𝔈` for every `K`, and its stress force is `(div 𝔇) • 𝔈`, which is
`ρ • E` with `4πρ = div E` for `K = 1` — i.e. Art. 108's `art108_force`. -/

/-- The electrostatic stress of a dielectric of capacity `K` (Art. 111): tension `p = K E²/8π`
along `E` with equal lateral pressure, `p_hk = K E_h E_k/4π − δ_hk K E²/8π`. -/
noncomputable def dielectricStress (K : ℝ) (E : Vec3) : Stress :=
  fun h k => K * (E h * E k) / fourPi - δ h k * (K * sq E) / (8 * Real.pi)

theorem dielectricStress_eq_smul (K : ℝ) (E : Vec3) :
    dielectricStress K E = K • componentForm E := by
  ext h k
  simp only [dielectricStress, componentForm, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `K = 1` is the library's `componentForm`: the dielectric stress is the old one. -/
theorem dielectricStress_one (E : Vec3) : dielectricStress 1 E = componentForm E := by
  rw [dielectricStress_eq_smul, one_smul]

theorem stressForce_const_smul {P : Vec3 → Stress} {x : Vec3} (c : ℝ)
    (hP : ∀ h k, DifferentiableAt ℝ (fun y => P y h k) x) :
    stressForce (fun y => c • P y) x = c • stressForce P x := by
  ext k
  simp only [stressForce, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => pd_const_mul h c (hP h k)

theorem div_const_smul {F : Vec3 → Vec3} {x : Vec3} (c : ℝ)
    (hF : ∀ i, DifferentiableAt ℝ (fun y => F y i) x) :
    div (fun y => c • F y) x = c * div F x := by
  simp only [div, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => pd_const_mul i c (hF i)

theorem traction_smul (c : ℝ) (P : Stress) (n : Vec3) :
    traction (c • P) n = c • traction P n := by
  ext k
  simp only [traction, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by ring

theorem normalStress_smul (c : ℝ) (P : Stress) (n : Vec3) :
    normalStress (c • P) n = c * normalStress P n := by
  simp [normalStress, traction_smul, dotProduct_smul, smul_dotProduct]

theorem sq_smul_unit (r : ℝ) {u : Vec3} (hu : u ⬝ᵥ u = 1) : sq (r • u) = r ^ 2 := by
  simp only [sq, dotProduct_smul, smul_dotProduct, hu, smul_eq_mul, mul_one]
  ring

/-- **Art. 111, the tension form for every capacity.** The tension of `dielectricStress K` along
`E = r u` is `½𝔇𝔈 = K r²/8π`: the energy per unit volume **is** the tension per unit area. -/
theorem dielectricStress_traction (K r : ℝ) {u : Vec3} (hu : u ⬝ᵥ u = 1) :
    traction (dielectricStress K (r • u)) u
      = ((1 / 2) * (((K / fourPi) • (r • u)) ⬝ᵥ (r • u))) • u := by
  have hsq := sq_smul_unit r hu
  have hdot : (r • u) ⬝ᵥ u = r := by simp [dotProduct_smul, hu]
  rw [dielectricStress_eq_smul, traction_smul, traction_componentForm, hdot,
    (art111_energy_eq_tension_all K (r • u)).1, hsq]
  ext k
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- **Art. 106/107 across the field, for every capacity**: the pressure of `dielectricStress K`
across a plane at right angles to `E` is `K E²/8π`, the same magnitude as the tension along `E`. -/
theorem dielectricStress_pressure {K : ℝ} {E n : Vec3} (hEn : E ⬝ᵥ n = 0) :
    traction (dielectricStress K E) n = -(K * sq E / (8 * Real.pi)) • n := by
  rw [dielectricStress_eq_smul, traction_smul, art106_pressure hEn]
  ext k
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- **Art. 107 with Art. 111, for every capacity `K`**: along `E = r u` a tension equal to the
energy per unit volume `½𝔇𝔈 = K r²/8π`, across `E` a pressure of the same magnitude. This is the
stress the library had only for `K = 1` (`art106_tension`, `art106_pressure`). -/
theorem dielectricStress_art107 (K r : ℝ) {u : Vec3} (hu : u ⬝ᵥ u = 1) :
    traction (dielectricStress K (r • u)) u
        = ((1 / 2) * (((K / fourPi) • (r • u)) ⬝ᵥ (r • u))) • u ∧
      ∀ n : Vec3, n ⬝ᵥ u = 0 →
        traction (dielectricStress K (r • u)) n
          = -((1 / 2) * (((K / fourPi) • (r • u)) ⬝ᵥ (r • u))) • n := by
  refine ⟨dielectricStress_traction K r hu, fun n hn => ?_⟩
  have hn' : (r • u) ⬝ᵥ n = 0 := by
    simp only [smul_dotProduct, smul_eq_mul]
    rw [dotProduct_comm u n, hn, mul_zero]
  rw [dielectricStress_pressure (K := K) (E := r • u) (n := n) hn',
    (art111_energy_eq_tension_all K (r • u)).1, neg_smul]

/-- **Art. 111's stress gives the force `(div 𝔇) • 𝔈`.** For a curl-free electromotive intensity
and `𝔇 = (K/4π) • 𝔈`. With `K = 1` this is Art. 108's `ρ • E` (see
`dielectricStress_K_one_force`). -/
theorem stressForce_dielectricStress {E : Vec3 → Vec3} {x : Vec3} {K : ℝ}
    (hE : ∀ i, DifferentiableAt ℝ (fun y => E y i) x) (hcurl : curl E x = 0) :
    stressForce (fun y => dielectricStress K (E y)) x
      = (div (fun y => (K / fourPi) • E y) x) • E x := by
  have hzero : crossProduct (curl E x) (E x) = 0 := by
    rw [hcurl]; ext i; fin_cases i <;> simp [cross_apply]
  have hfun : (fun y : Vec3 => dielectricStress K (E y)) = fun y => K • componentForm (E y) := by
    funext y; exact dielectricStress_eq_smul K (E y)
  rw [hfun, stressForce_const_smul K (fun h k => differentiableAt_componentForm hE h k),
    stressForce_componentForm hE, hzero, smul_zero, add_zero, div_const_smul (K / fourPi) hE]
  ext k
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Art. 111/108 in a dielectric:** if `div 𝔇 = ρ` with `𝔇 = (K/4π) • 𝔈`, the Art. 111 stress
exerts the force `ρ • 𝔈` per unit volume. -/
theorem art111_force_dielectric {E : Vec3 → Vec3} {x : Vec3} {K ρ : ℝ}
    (hE : ∀ i, DifferentiableAt ℝ (fun y => E y i) x) (hcurl : curl E x = 0)
    (hD : div (fun y => (K / fourPi) • E y) x = ρ) :
    stressForce (fun y => dielectricStress K (E y)) x = ρ • E x := by
  rw [stressForce_dielectricStress hE hcurl, hD]

/-- **`K = 1` recovers `art108_force`**: with `div E = 4πρ` and `curl E = 0` the *same*
`componentForm`-type stress (here `dielectricStress 1`) gives `ρ • E`. -/
theorem dielectricStress_K_one_force {E : Vec3 → Vec3} {x : Vec3} {ρ : ℝ}
    (hE : ∀ i, DifferentiableAt ℝ (fun y => E y i) x) (hcurl : curl E x = 0)
    (h77 : div E x = fourPi * ρ) :
    stressForce (fun y => dielectricStress 1 (E y)) x = ρ • E x := by
  have hD : div (fun y => (1 / fourPi) • E y) x = ρ := by
    rw [div_const_smul (1 / fourPi) hE, h77]
    field_simp
  rw [art111_force_dielectric hE hcurl hD]

/-! ## 8. Art. 792: what `art792_radiation_pressure` checks and what it does not

`art792_radiation_pressure` takes `uE, uH` unit vectors "along `E`, `H`" — but the proof never uses
`uE ⬝ᵥ uE = 1`, `E = √(E·E) • uE`, `uH ⬝ᵥ uH = 1`, `H = √(H·H) • uH`; the stress it writes uses
`uE`, `uH` and `sq E`, `sq H` only. So the theorem is a statement about the *tension form*, not
about the stress of the field `E`: it cannot tell `componentForm E` (tension `E²/8π`) from the
Art. 111 dielectric stress (tension `K E²/8π`). Re-proved below without the unused hypotheses, and
then re-proved for the stress actually built from the fields. -/

theorem art792_radiation_pressure_weak (K μ : ℝ) {E H uE uH n : Vec3} (hn : n ⬝ᵥ n = 1)
    (hEn : uE ⬝ᵥ n = 0) (hHn : uH ⬝ᵥ n = 0) :
    normalStress (tensionWithLateralPressure (K * sq E / (8 * Real.pi)) uE +
        tensionWithLateralPressure (μ * sq H / (8 * Real.pi)) uH) n =
      -(electrostaticEnergy631 E ((K / fourPi) • E) + electrokineticEnergy636 (μ • H) H) := by
  rw [normalStress_add, normalStress_tensionWithLateralPressure _ hn hEn,
    normalStress_tensionWithLateralPressure _ hn hHn, (energy_isotropic K μ E H).1,
    (energy_isotropic K μ E H).2]
  ring

theorem normalStress_componentForm_of_perp {v n : Vec3} (hn : n ⬝ᵥ n = 1)
    (hv : v ⬝ᵥ n = 0) : normalStress (componentForm v) n = -(sq v / (8 * Real.pi)) := by
  simp only [normalStress, art106_pressure hv]
  simp [dotProduct_smul, hn]

theorem normalStress_dielectricStress {K : ℝ} {E n : Vec3} (hn : n ⬝ᵥ n = 1)
    (hEn : E ⬝ᵥ n = 0) :
    normalStress (dielectricStress K E) n = -(K * sq E / (8 * Real.pi)) := by
  rw [dielectricStress_eq_smul, normalStress_smul, normalStress_componentForm_of_perp hn hEn]
  ring

/-- **The content of `art792_radiation_pressure` is the tension-form algebra alone.** For *any*
two tensions `p₁, p₂` along directions transverse to `n`, the normal stress of the superposed
stress is `−(p₁ + p₂)`: no field, energy density or Maxwell article enters. `art792_radiation_pressure`
is this with `p₁ = K E²/8π`, `p₂ = μ H²/8π`, which are exactly the energy densities, so its
conclusion is an identity in the tension parameters rather than a derivation from the stress of the
fields (that derivation is `art792_with_field_stress`). -/
theorem art792_tautology {p₁ p₂ : ℝ} {uE uH n : Vec3} (hn : n ⬝ᵥ n = 1)
    (hEn : uE ⬝ᵥ n = 0) (hHn : uH ⬝ᵥ n = 0) :
    normalStress (tensionWithLateralPressure p₁ uE + tensionWithLateralPressure p₂ uH) n
      = -(p₁ + p₂) := by
  rw [normalStress_add, normalStress_tensionWithLateralPressure _ hn hEn,
    normalStress_tensionWithLateralPressure _ hn hHn]
  ring

/-- **Art. 792 with the stresses built from the fields.** Dielectric of capacity `K` with the
Art. 111 stress, and `B = μH` with the Art. 641 stress: the pressure across the wave front is
`K E²/8π + H²/8π` — the magnetic half is *independent of `μ`* (Arts. 641–642). -/
theorem art792_with_field_stress {K μ : ℝ} {E H n : Vec3} (hn : n ⬝ᵥ n = 1)
    (hEn : E ⬝ᵥ n = 0) (hHn : H ⬝ᵥ n = 0) :
    normalStress (dielectricStress K E + magneticStress641 (μ • H) H) n
      = -(K * sq E / (8 * Real.pi) + sq H / (8 * Real.pi)) := by
  rw [normalStress_add, normalStress_dielectricStress hn hEn,
    art642_normalStress_transverse μ hn hHn]
  ring

/-- **Art. 792's "pressure equals the whole energy" holds iff `μ = 1`** (Art. 792 cites Art. 643,
the unmagnetized case `B = H`), for every capacity `K` and every transverse `E, H`. This extends
`art642_vs_art792` from the magnetic half alone to the full superposed stress. -/
theorem art792_energy_iff {K μ : ℝ} {E H n : Vec3} (hn : n ⬝ᵥ n = 1)
    (hEn : E ⬝ᵥ n = 0) (hHn : H ⬝ᵥ n = 0) :
    normalStress (dielectricStress K E + magneticStress641 (μ • H) H) n
        = -(electrostaticEnergy631 E ((K / fourPi) • E) + electrokineticEnergy636 (μ • H) H)
      ↔ (μ = 1 ∨ sq H = 0) := by
  rw [art792_with_field_stress hn hEn hHn, (energy_isotropic K μ E H).1,
    (energy_isotropic K μ E H).2]
  constructor
  · intro h
    have h' : (μ - 1) * sq H = 0 := by field_simp at h; linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · right; exact h1
  · rintro (h | h)
    · subst h; ring
    · rw [h]; ring


/-! ## 9. Rational evaluations of the printed formulas against the Lean definitions

Each theorem evaluates a Lean definition at explicit rational vectors and compares with the
displayed formula of the article, carried out by hand in rational multiples of `1/π`. -/

/-- The diagonal entry of Art. 641 eq. (15) as printed, `P_xx = (aα − ½ℌ²)/4π`, for any `B, H`. -/
theorem magneticStress641_diag (B H : Vec3) (h : Fin 3) :
    magneticStress641 B H h h = (B h * H h - sq H / 2) / (4 * Real.pi) := by
  simp [magneticStress641, δ, fourPi]
  field_simp
  ring

/-- The off-diagonal entry of Art. 641 eq. (15) as printed, `P_hk = B_h H_k/4π` for `h ≠ k`. -/
theorem magneticStress641_offdiag {B H : Vec3} {h k : Fin 3} (hhk : h ≠ k) :
    magneticStress641 B H h k = B h * H k / (4 * Real.pi) := by
  simp [magneticStress641, δ, if_neg hhk, fourPi]

/-- **Art. 641 eq. (15)**, `B = (1,2,3)`, `H = (½,−1,2)`: `P_xx = −17/32π`, `P_yz = bγ/4π = 1/π`,
`P_zy = cβ/4π = −3/4π`; the printed `xx` formula `(aα − ½ℌ²)/4π` gives the same `−17/32π`. -/
theorem art641_numeric :
    magneticStress641 ![1, 2, 3] ![1 / 2, -1, 2] 0 0 = -17 / (32 * Real.pi) ∧
    magneticStress641 ![1, 2, 3] ![1 / 2, -1, 2] 1 2 = 1 / Real.pi ∧
    magneticStress641 ![1, 2, 3] ![1 / 2, -1, 2] 2 1 = -3 / (4 * Real.pi) ∧
    (1 * (1 / 2) - sq ![1 / 2, -1, 2] / 2) / (4 * Real.pi) = -17 / (32 * Real.pi) := by
  have h1 : magneticStress641 ![1, 2, 3] ![1 / 2, -1, 2] 0 0 = -17 / (32 * Real.pi) := by
    rw [magneticStress641_diag]
    simp [sq_eq, dotProduct, fourPi]
    field_simp
    ring
  refine ⟨h1, ?_, ?_, ?_⟩ <;>
    simp [magneticStress641, δ, fourPi, sq_eq, dotProduct] <;>
    try field_simp <;> try ring

/-- **Art. 642 eqs. (17)–(18)** in the `3-4-5` bisector frame: `sin ε = 3/5`, `cos ε = 4/5`,
`𝔅 = 2`, `ℌ = 3`, so `B = (8/5,−6/5,0)`, `H = (12/5,9/5,0)`. The stress is
`−ℌ²/8π · 1 + (𝔅ℌcos²ε/4π) e₀e₀ᵀ − (𝔅ℌsin²ε/4π) e₁e₁ᵀ + (𝔅ℌcosε sinε/4π)(e₀e₁ᵀ − e₁e₀ᵀ)`
with `−ℌ²/8π = −225/200π`, `𝔅ℌcos²ε/4π = 24/25π`, `𝔅ℌsin²ε/4π = 54/100π`, and couple
`𝔅ℌ sin2ε/4π = 36/25π`; the same numbers come out of the printed decomposition. -/
theorem art642_bisector_numeric :
    magneticStress641 ![8 / 5, -6 / 5, 0] ![12 / 5, 9 / 5, 0] 0 0 = -33 / (200 * Real.pi) ∧
    magneticStress641 ![8 / 5, -6 / 5, 0] ![12 / 5, 9 / 5, 0] 1 1 = -333 / (200 * Real.pi) ∧
    magneticStress641 ![8 / 5, -6 / 5, 0] ![12 / 5, 9 / 5, 0] 2 2 = -9 / (8 * Real.pi) ∧
    magneticStress641 ![8 / 5, -6 / 5, 0] ![12 / 5, 9 / 5, 0] 0 1 = 18 / (25 * Real.pi) ∧
    magneticStress641 ![8 / 5, -6 / 5, 0] ![12 / 5, 9 / 5, 0] 1 0 = -18 / (25 * Real.pi) ∧
    couple (magneticStress641 ![8 / 5, -6 / 5, 0] ![12 / 5, 9 / 5, 0]) 2
      = 36 / (25 * Real.pi) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [magneticStress641, couple, δ, fourPi, sq_eq] <;>
    try field_simp <;> try ring

/-- The printed decomposition of Art. 642 eq. (17) at `sin ε = 3/5`, `cos ε = 4/5`: same numbers. -/
theorem art642_bisector_arithmetic :
    (-(9 / (8 * Real.pi)) + 6 * (16 / 25) / (4 * Real.pi) = -33 / (200 * Real.pi)) ∧
    (-(9 / (8 * Real.pi)) - 6 * (9 / 25) / (4 * Real.pi) = -333 / (200 * Real.pi)) ∧
    (6 * (24 / 25) / (4 * Real.pi) = 36 / (25 * Real.pi)) := by
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> norm_num

/-- **Art. 642 eq. (18)** with `B = 3H = (0,0,6)`, `H = (0,0,2)`: `P_zz = 5/2π = (𝔅ℌ − ½ℌ²)/4π`
with `𝔅ℌ = 12`, `ℌ² = 4`, and `P_xx = P_yy = −1/2π = −ℌ²/8π` (hydrostatic pressure `ℌ²/8π` plus
longitudinal tension `𝔅ℌ/4π`). -/
theorem art642_along_H_numeric :
    magneticStress641 ![0, 0, 6] ![0, 0, 2] 2 2 = 5 / (2 * Real.pi) ∧
    magneticStress641 ![0, 0, 6] ![0, 0, 2] 0 0 = -1 / (2 * Real.pi) ∧
    magneticStress641 ![0, 0, 6] ![0, 0, 2] 1 1 = -1 / (2 * Real.pi) ∧
    (1 * (12 - 2) / (4 * Real.pi) = 5 / (2 * Real.pi)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [magneticStress641, δ, fourPi, sq_eq, dotProduct] <;>
    try field_simp <;> try ring

/-- **Art. 792, numerically.** Dielectric `K = 2`, permeability `μ = 3`, `E = (1,0,0)`,
`H = (0,2,0)` in the wave front (normal `(0,0,1)`): the pressure across the front is
`−(2/8π + 4/8π) = −3/4π` while the energy is `2/8π + 3·4/8π = 7/4π` — Maxwell's "pressure equals
the whole energy" fails for `μ ≠ 1`, as `art792_energy_iff` says. With `K = μ = 1` both are `5/8π`. -/
theorem art792_numeric :
    normalStress (dielectricStress 2 ![1, 0, 0] + magneticStress641 (3 • ![0, 2, 0]) ![0, 2, 0])
        ![0, 0, 1] = -(3 / (4 * Real.pi)) ∧
    (electrostaticEnergy631 ![1, 0, 0] ((2 / fourPi) • ![1, 0, 0]) +
        electrokineticEnergy636 (3 • ![0, 2, 0]) ![0, 2, 0]) = 7 / (4 * Real.pi) ∧
    normalStress (dielectricStress 1 ![1, 0, 0] + magneticStress641 (1 • ![0, 2, 0]) ![0, 2, 0])
        ![0, 0, 1] = -(5 / (8 * Real.pi)) ∧
    (electrostaticEnergy631 ![1, 0, 0] ((1 / fourPi) • ![1, 0, 0]) +
        electrokineticEnergy636 (1 • ![0, 2, 0]) ![0, 2, 0]) = 5 / (8 * Real.pi) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [normalStress, traction, dielectricStress, magneticStress641, electrostaticEnergy631,
      electrokineticEnergy636, δ, fourPi, sq_eq, dotProduct, Fin.sum_univ_three] <;>
    try field_simp <;> try ring

/-- **Art. 111, numerically**, `K = 3`, `𝔈 = (1,2,2)`, `𝔇 = (3/4π)𝔈`, `|𝔈|² = 9`:
`p = ½𝔇𝔈 = 27/8π = (2π/K)𝔇²`, and the tension of the Art. 111 stress along `û = 𝔈/3` is `p û`. -/
theorem art111_numeric :
    (1 / 2) * (((3 / fourPi) • ![1, 2, 2]) ⬝ᵥ ![1, 2, 2]) = 27 / (8 * Real.pi) ∧
    (2 * Real.pi / 3) * sq ((3 / fourPi) • ![1, 2, 2]) = 27 / (8 * Real.pi) ∧
    traction (dielectricStress 3 ![1, 2, 2]) ![1 / 3, 2 / 3, 2 / 3]
      = (27 / (8 * Real.pi)) • ![1 / 3, 2 / 3, 2 / 3] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sq_eq, dotProduct, fourPi, Fin.sum_univ_three]; field_simp; ring
  · have hsq : sq ((3 / fourPi) • ![1, 2, 2]) = 81 / (16 * Real.pi ^ 2) := by
      simp [sq, dotProduct, Fin.sum_univ_three, fourPi]
      field_simp
      ring
    rw [hsq]
    field_simp
    ring
  · ext k
    fin_cases k <;>
      simp [traction, dielectricStress, δ, fourPi, sq_eq, dotProduct, Fin.sum_univ_three] <;>
      field_simp <;> norm_num


/-! ## 10. Two sharp statements of the gaps found

* For `K ≠ 1` the library's `componentForm E` is *not* Art. 111's stress: its tension is
  `E²/8π`, not `K E²/8π`. This is the exact content of the gap repaired in §7.
* Art. 642's couple really turns each element from `B` toward `H`: for `0 < ε < π/2` it is
  strictly positive about `z`. -/

theorem sq_smul' (c : ℝ) (v : Vec3) : sq (c • v) = c ^ 2 * sq v := by
  simp only [sq, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- **The `K ≠ 1` gap, exactly.** If `K ≠ 1` and `E ≠ 0`, the tension of the library's
`componentForm E` along `E` is *not* Art. 111's `p = K E²/8π`: for `K ≠ 1` the stress of Art. 111
must be `dielectricStress K E`, which no theorem of the library provided. -/
theorem art111_componentForm_not_dielectric {K : ℝ} {E : Vec3} (hE : sq E ≠ 0) (hK : K ≠ 1) :
    traction (componentForm E) E ≠ (K * sq E / (8 * Real.pi)) • E := by
  rw [art106_tension]
  intro h
  have hsub : (sq E / (8 * Real.pi)) • E - (K * sq E / (8 * Real.pi)) • E = 0 := by
    rw [h, sub_self]
  rw [← sub_smul] at hsub
  have hsq2 : ((sq E / (8 * Real.pi)) - (K * sq E / (8 * Real.pi))) ^ 2 * sq E = 0 := by
    rw [← sq_smul', hsub]; simp [sq]
  have hsq' : sq E / (8 * Real.pi) ≠ 0 := div_ne_zero hE (by positivity)
  have hc : ((sq E / (8 * Real.pi)) - (K * sq E / (8 * Real.pi))) = 0 := by
    rcases mul_eq_zero.mp hsq2 with h1 | h1
    · rw [pow_two] at h1
      exact mul_self_eq_zero.mp h1
    · exact absurd h1 hE
  have e : (sq E / (8 * Real.pi)) - (K * sq E / (8 * Real.pi))
      = (1 - K) * (sq E / (8 * Real.pi)) := by ring
  rw [e] at hc
  rcases mul_eq_zero.mp hc with h1 | h1
  · exact hK (by linarith)
  · exact hsq' h1

/-- **Art. 642, the couple's direction.** For `𝔅, ℌ > 0` and `0 < ε < π/2`, the couple of the
bisector stress about `z` is strictly positive, i.e. it turns the element from `B` (at angle
`−ε`) toward `H` (at angle `+ε`): `𝔅ℌ sin 2ε/4π > 0`. -/
theorem art642_couple_pos {𝔅 ℌ ε : ℝ} (h𝔅 : 0 < 𝔅) (hℌ : 0 < ℌ)
    (hε : 0 < ε) (hε' : ε < Real.pi / 2) :
    0 < couple (magneticStress641 ![𝔅 * Real.cos ε, -(𝔅 * Real.sin ε), 0]
      ![ℌ * Real.cos ε, ℌ * Real.sin ε, 0]) 2 := by
  rw [(art642_bisector 𝔅 ℌ ε).2]
  have h2 : 0 < Real.sin (2 * ε) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  positivity

end Maxwell
