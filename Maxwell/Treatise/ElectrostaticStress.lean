/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Basic

/-!
# Electrostatic stress (Treatise 1873, vol. I, Arts. 107–111; 2nd ed. 1881, vol. I, Arts. 103–106)

Three things are kept apart here, in Maxwell's order.

1. **1873, Arts. 107–108.** A *tension* `p` along the resultant force `R` with an *equal pressure*
   `p` in every perpendicular direction, `R² = 8πp`; Art. 108 builds this from his
   superposition formula for three tensions along perpendicular directions (eqs. (1)–(5)),
   writes the components (eq. (6)), and differentiates them to recover the force `ρ R` on the
   electricity in an element (eqs. (7)–(10)), using `dX/dx + dY/dy + dZ/dz = 4πρ` (Art. 77).
2. **1881, Arts. 103–105.** The rewritten chapter (Niven's preface: the first nine chapters were
   revised by Maxwell) starts from the potential `Ψ` with `∇²Ψ = 4πρ` and writes the components
   (eq. (14)) `p_xx = (1/8π)((dΨ/dx)² − (dΨ/dy)² − (dΨ/dz)²)`, `p_xy = (1/4π)(dΨ/dx)(dΨ/dy)`; the
   point of Art. 105 is the "direct action" test: the action must be expressible as a surface
   integral over *any* separating surface. The local identity is proved here; the surface
   integral form is stated in `Maxwell.Statements`.
3. **1881, Art. 106.** The type of the stress: tension along the electromotive intensity,
   pressure of the same value across it — "two of its principal stresses equal to each other,
   and the third has the same value with the sign reversed."

What Maxwell did **not** do is also kept: Art. 111 (1873, p. 132) "I have not been able to make
the next step, namely, to account by mechanical considerations for these stresses in the
dielectric. I therefore leave the theory at this point." Nothing in this file supplies such a
mechanism; see `Maxwell.Sources.art111`.

Sign conventions. Maxwell's `∇²` is `−(d²/dx² + d²/dy² + d²/dz²)` (footnote to Art. 616,
vol. II, p. 235, "the negative sign is employed here in order to make our expressions consistent
with those in which Quaternions are employed"), so his `∇²Ψ = 4πρ` is `−ΔΨ = 4πρ` below.

Local sources: `/workspace/maxwell_reread/n_electricandmagne01maxwrich.txt` (1873, vol. I) and
`/workspace/maxwell_reread/n_treatiseonelectr01maxwrich.txt` (1881, vol. I). The 1873 formula
typography is badly garbled in the OCR; the algebra was checked by re-deriving it.
-/

namespace Maxwell

open Matrix

/-! ## 1873, Art. 108: superposition of tensions along given directions -/

/-- Treatise 1873, vol. I, Art. 108, eqs. (1)–(2), pp. 128–129: three tensions `t a` along the
directions with direction-cosines `dir a` give `p_hk = ∑_a t_a · l_a(h) · l_a(k)`
(e.g. `p_xx = p l² + p' l'² + p'' l''²`). -/
def art108Stress (dir : Fin 3 → Vec3) (t : Fin 3 → ℝ) : Stress :=
  fun h k => ∑ a, t a * dir a h * dir a k

/-- Three mutually perpendicular unit directions. -/
def IsOrthonormalFrame (dir : Fin 3 → Vec3) : Prop := ∀ a b, dir a ⬝ᵥ dir b = δ a b

/-- Treatise 1873, vol. I, Art. 107 (p. 127): "a tension `p` at every point of the medium in the
direction of the resultant force `R` … in every direction perpendicular to `R` there is a
pressure `p`." As a stress along the unit direction `u`: `p (2 u_h u_k − δ_hk)` — Maxwell's own
decomposition at the end of Art. 106 (p. 126): "the tension `p` may be considered as a pressure
`p` combined with a tension `2p`." -/
def tensionWithLateralPressure (p : ℝ) (u : Vec3) : Stress :=
  fun h k => p * (2 * u h * u k - δ h k)

theorem sum_frame_eq_delta {dir : Fin 3 → Vec3} (hdir : IsOrthonormalFrame dir) (h k : Fin 3) :
    ∑ a, dir a h * dir a k = δ h k := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of dir
  have h1 : M * Mᵀ = 1 := by
    ext a b
    simpa [M, Matrix.mul_apply, dotProduct, δ, Matrix.one_apply] using hdir a b
  have h2 : Mᵀ * M = 1 := mul_eq_one_comm.mp h1
  have := congrFun (congrFun h2 h) k
  simpa [M, Matrix.mul_apply, δ, Matrix.one_apply] using this

/-- **Treatise 1873, vol. I, Art. 108, eqs. (3)–(5), p. 129.** "In the case of the electrical
tension and pressure the pressures are numerically equal to the tension at every point, and are
in directions at right angles to the tension and to each other. Hence, putting `p' = p'' = −p`"
the superposed stress of Art. 108 is the tension-with-lateral-pressure of Art. 107. -/
theorem art108_superposition {dir : Fin 3 → Vec3} (hdir : IsOrthonormalFrame dir) (p : ℝ) :
    art108Stress dir ![p, -p, -p] = tensionWithLateralPressure p (dir 0) := by
  ext h k
  have hs := sum_frame_eq_delta hdir h k
  simp only [Fin.sum_univ_three] at hs
  simp only [art108Stress, tensionWithLateralPressure, Fin.sum_univ_three]
  simp
  rw [← hs]; ring

/-- The component form of the electrostatic stress, in terms of the components `X, Y, Z` of the
resultant force (Treatise 1873, vol. I, Art. 108, eq. (6), p. 129) or of the electromotive
intensity (1881, Art. 105, eq. (14), p. 147): `p_hk = X_h X_k / 4π − δ_hk (X² + Y² + Z²)/8π`. -/
noncomputable def componentForm (v : Vec3) : Stress :=
  fun h k => v h * v k / fourPi - δ h k * sq v / (8 * Real.pi)

/-- **Treatise 1873, vol. I, Art. 108, eq. (6), p. 129** (with `p = R²/8π`, Art. 107, and
`R l = X`, `R m = Y`, `R n = Z`): the tension along `R` with equal lateral pressure has the
components of `componentForm R`. Here `R = r u` with `u` a unit vector (`r` may be negative;
only `r²` enters). -/
theorem art108_components (r : ℝ) {u : Vec3} (hu : u ⬝ᵥ u = 1) :
    tensionWithLateralPressure (r ^ 2 / (8 * Real.pi)) u = componentForm (r • u) := by
  have hsq : sq (r • u) = r ^ 2 := by
    simp [sq, dotProduct_smul, smul_dotProduct, hu]; ring
  ext h k
  simp only [tensionWithLateralPressure, componentForm, hsq, fourPi, Pi.smul_apply, smul_eq_mul]
  field_simp; ring

/-- The explicit `xx` and `xy` components, as printed: `p_xx = (X² − Y² − Z²)/8π`,
`p_xy = XY/4π` (Treatise 1873, vol. I, Art. 108, eq. (6), p. 129; 1881, vol. I, Art. 105,
eq. (14), p. 147, there with `X = −dΨ/dx` etc.). -/
theorem componentForm_xx_xy (X Y Z : ℝ) :
    componentForm ![X, Y, Z] 0 0 = (X ^ 2 - Y ^ 2 - Z ^ 2) / (8 * Real.pi) ∧
    componentForm ![X, Y, Z] 0 1 = X * Y / (4 * Real.pi) ∧
    componentForm ![X, Y, Z] 1 1 = (Y ^ 2 - Z ^ 2 - X ^ 2) / (8 * Real.pi) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [componentForm, sq_eq, δ, fourPi] <;> field_simp <;> ring

/-! ## The force on an element, from the stress (1873 Art. 108; 1881 Arts. 104–105) -/

theorem pd_componentForm {F : Vec3 → Vec3} {x : Vec3}
    (hF : ∀ i, DifferentiableAt ℝ (fun y => F y i) x) (h k : Fin 3) :
    pd h (fun y => componentForm (F y) h k) x =
      (pd h (fun y => F y h) x * F x k + F x h * pd h (fun y => F y k) x) / fourPi
      - δ h k * (2 * (F x 0 * pd h (fun y => F y 0) x + F x 1 * pd h (fun y => F y 1) x
          + F x 2 * pd h (fun y => F y 2) x)) / (8 * Real.pi) := by
  have e : (fun y => componentForm (F y) h k) = fun y =>
      (1 / fourPi) * (F y h * F y k) - (δ h k / (8 * Real.pi)) *
        (F y 0 * F y 0 + F y 1 * F y 1 + F y 2 * F y 2) := by
    funext y; simp only [componentForm, sq_eq]; ring
  have h0 := hF 0; have h1 := hF 1; have h2 := hF 2; have hh := hF h; have hk := hF k
  rw [e, pd_sub _ (by fun_prop) (by fun_prop), pd_const_mul _ _ (by fun_prop),
    pd_const_mul _ _ (by fun_prop), pd_mul _ hh hk, pd_add _ (by fun_prop) (by fun_prop),
    pd_add _ (by fun_prop) (by fun_prop), pd_mul _ h0 h0, pd_mul _ h1 h1, pd_mul _ h2 h2]
  ring

/-- The resultant force per unit volume of the stress `componentForm F` for *any* differentiable
field `F`: `(div F / 4π) F + (1/4π) (curl F) × F`. This is the algebra behind both Art. 108
(electric, 1873 vol. I, p. 130) and Art. 643 (magnetic, 1873 vol. II, pp. 256–257); it is
bookkeeping, not a claim of Maxwell's, and each use below adds his own hypotheses. -/
theorem stressForce_componentForm {F : Vec3 → Vec3} {x : Vec3}
    (hF : ∀ i, DifferentiableAt ℝ (fun y => F y i) x) :
    stressForce (fun y => componentForm (F y)) x =
      (div F x / fourPi) • F x + (1 / fourPi) • crossProduct (curl F x) (F x) := by
  ext k
  simp only [stressForce, pd_componentForm hF, Fin.sum_univ_three, div, curl, cross_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, δ]
  fin_cases k <;> simp <;> field_simp <;> ring

/-- **Treatise 1873, vol. I, Art. 108, eqs. (7)–(10), p. 130.** Differentiating the components
(6) and using Art. 77, `dX/dx + dY/dy + dZ/dz = 4πρ`, the internal force per unit volume is
`ξ = ρX, η = ρY, ζ = ρZ`: "the resultant of the tensions and pressures which we have supposed to
act upon the surface of the element is a force whose components are the same as those of the
force, which, in the ordinary theory, is ascribed to the action of electrified bodies on the
electricity within the element."

Hypotheses, as in the text: `R` is the resultant force of an electrostatic field, so it has no
curl (it is derived from the potential `V`, Art. 108 works throughout with `−dV/dx`), and Art. 77
gives its divergence. Pointwise at `x`; Maxwell's conclusion for "any portion of the medium,
however bounded" (p. 131) is the integrated form, stated in `Maxwell.Statements`. -/
theorem art108_force {R : Vec3 → Vec3} {x : Vec3} {ρ : ℝ}
    (hR : ∀ i, DifferentiableAt ℝ (fun y => R y i) x)
    (hcurl : curl R x = 0) (hArt77 : div R x = fourPi * ρ) :
    stressForce (fun y => componentForm (R y)) x = ρ • R x := by
  rw [stressForce_componentForm hR, hcurl, hArt77]
  ext k
  simp [fourPi, Real.pi_ne_zero]

/-- Maxwell's `∇²`, *with his sign*: `∇² = −(d²/dx² + d²/dy² + d²/dz²)` (footnote to Art. 616,
vol. II, p. 235). -/
noncomputable def maxwellNabla2 (Ψ : Vec3 → ℝ) (x : Vec3) : ℝ :=
  - ∑ i, pd i (fun y => pd i Ψ y) x

/-- The 1881 electrostatic stress from the potential (Treatise 1881, vol. I, Art. 105, eq. (14),
p. 147): `p_xx = (1/8π)((dΨ/dx)² − (dΨ/dy)² − (dΨ/dz)²)`, `p_xy = (1/4π)(dΨ/dx)(dΨ/dy)`, etc. -/
noncomputable def stress1881 (Ψ : Vec3 → ℝ) (x : Vec3) : Stress := componentForm (grad Ψ x)

/-- The 1881 components are unchanged on replacing `dΨ/dx` by the electromotive intensity
`E = −dΨ/dx` (Art. 106, p. 148). -/
theorem stress1881_eq_componentForm_neg_grad (Ψ : Vec3 → ℝ) (x : Vec3) :
    stress1881 Ψ x = componentForm (-grad Ψ x) := by
  ext h k; simp [stress1881, componentForm, sq]

theorem curl_grad_eq_zero {Ψ : Vec3 → ℝ} {x : Vec3} (hΨ : ContDiffAt ℝ 2 Ψ x) :
    curl (grad Ψ) x = 0 := by
  ext i
  fin_cases i <;> simp [curl, grad, pd_pd_comm hΨ]

/-- **Treatise 1881, vol. I, Arts. 103–105, eqs. (6), (14)–(15), pp. 145–147.** With
`∇²Ψ = 4πρ` (Maxwell's sign), the stress (14) produces the force `−ρ dΨ/dx` per unit volume, so
that `A = ∭ (dp_xx/dx + dp_xy/dy + dp_xz/dz) dx dy dz` (eq. (15)) is the `x`-component of the
force on the electrified system. Pointwise, for a `C²` potential. -/
theorem art105_force {Ψ : Vec3 → ℝ} {x : Vec3} {ρ : ℝ} (hΨ : ContDiffAt ℝ 2 Ψ x)
    (hPoisson : maxwellNabla2 Ψ x = fourPi * ρ) :
    stressForce (fun y => stress1881 Ψ y) x = ρ • (- grad Ψ x) := by
  have hdiff : ∀ i, DifferentiableAt ℝ (fun y => grad Ψ y i) x := fun i => differentiableAt_pd hΨ i
  have h := stressForce_componentForm hdiff
  simp only [stress1881]
  rw [h, curl_grad_eq_zero hΨ]
  have hdiv : div (grad Ψ) x = - (fourPi * ρ) := by
    rw [← hPoisson]; simp [div, maxwellNabla2, grad]
  rw [hdiv]
  ext k
  simp [fourPi]
  field_simp

/-! ## 1881, Art. 106: the type of the stress -/

theorem componentForm_transpose (v : Vec3) : (componentForm v)ᵀ = componentForm v := by
  ext h k; simp [componentForm, δ, eq_comm]; ring

theorem traction_componentForm (v n : Vec3) :
    traction (componentForm v) n = (v ⬝ᵥ n / fourPi) • v - (sq v / (8 * Real.pi)) • n := by
  ext k
  simp only [traction, componentForm, Fin.sum_univ_three, δ, dotProduct, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  fin_cases k <;> simp <;> ring

/-- **Treatise 1881, vol. I, Art. 106, p. 148** (and 1873, Art. 107): across an element whose
normal is along the electromotive intensity `E`, the force is "normal to the element and
directed outwards, that is to say, it is a tension like that of a rope, and its value per unit of
area is `E²/8π`." -/
theorem art106_tension (E : Vec3) :
    traction (componentForm E) E = (sq E / (8 * Real.pi)) • E := by
  rw [traction_componentForm]
  ext k; simp [sq, fourPi]; ring

/-- **Treatise 1881, vol. I, Art. 106, p. 149:** across an element at right angles to the
equipotential surfaces (normal `n ⊥ E`), "the force which acts on it is normal to the surface,
and its numerical value per unit of area is the same as in the former case, but … it is a
pressure instead of a tension." -/
theorem art106_pressure {E n : Vec3} (hn : E ⬝ᵥ n = 0) :
    traction (componentForm E) n = -(sq E / (8 * Real.pi)) • n := by
  rw [traction_componentForm, hn]; ext k; simp

/-- **Treatise 1881, vol. I, Art. 106, p. 149:** "The stress as thus defined is not of the most
general type, for it has two of its principal stresses equal to each other, and the third has
the same value with the sign reversed." For `E ≠ 0` with `E, e₁, e₂` mutually perpendicular,
the principal values are `E²/8π` along `E` and `−E²/8π` along `e₁` and `e₂`, and the stress is
symmetric. -/
theorem art106_principal {E e₁ e₂ : Vec3} (h₁ : E ⬝ᵥ e₁ = 0) (h₂ : E ⬝ᵥ e₂ = 0) :
    (componentForm E)ᵀ = componentForm E ∧
    traction (componentForm E) E = (sq E / (8 * Real.pi)) • E ∧
    traction (componentForm E) e₁ = (-(sq E / (8 * Real.pi))) • e₁ ∧
    traction (componentForm E) e₂ = (-(sq E / (8 * Real.pi))) • e₂ :=
  ⟨componentForm_transpose E, art106_tension E, by rw [art106_pressure h₁, neg_smul],
    by rw [art106_pressure h₂, neg_smul]⟩

/-! ## 1873, Art. 111: energy per unit volume equals the tension per unit area -/

/-- **Treatise 1873, vol. I, Art. 111, p. 134:** "the energy in unit of volume of the medium is
numerically equal to the electric tension on unit of area, both quantities being equal to half
the product of the displacement and the resultant electromotive force." With the displacement
`D = K R / 4π` of a dielectric of specific inductive capacity `K` (Art. 111, I, and Art. 75),
half the product is `K R²/8π`; for `K = 1` it is the tension `p = R²/8π` of Art. 107.

Sharpening: Art. 107 states the tension for the case `R² = 8πp` without `K`; Art. 111 asserts
equality with `½ D·R` in a dielectric. The formal statement records the two separately, and
equality with Art. 107's `p` holds exactly when `K = 1`. -/
theorem art111_energy_eq_tension (K : ℝ) (R : Vec3) :
    (1 / 2) * (R ⬝ᵥ ((K / fourPi) • R)) = K * sq R / (8 * Real.pi) ∧
    (1 / 2) * (R ⬝ᵥ ((1 / fourPi) • R)) = sq R / (8 * Real.pi) := by
  constructor <;> simp [sq, dotProduct_smul, fourPi] <;> field_simp <;> ring

end Maxwell
