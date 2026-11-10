/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

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
   integral over *any* separating surface. The local identity is proved here, and so is the
   integrated form on boxes (`art105_directAction`, by Mathlib's divergence theorem). Maxwell's
   "any closed surface" is wider than boxes and is not formalized. Maxwell is explicit that the
   components are physical only if the action is through a medium; otherwise they are "mere
   abbreviated forms … having no physical significance" (`Maxwell.Sources.art105_1881`).
3. **1881, Art. 106.** The type of the stress: tension along the electromotive intensity,
   pressure of the same value across it — "two of its principal stresses equal to each other,
   and the third has the same value with the sign reversed."

What Maxwell did **not** do is also kept: Art. 107 (1873, p. 128) calls the illustration "merely
an explanation of what is meant by the tension and pressure, not as a physical theory to account
for them"; Art. 110 (p. 132) "we have made only one step in the theory of the action of the
medium"; and Art. 111 (1873, p. 132, retained in 1881) "I have not been able to make the next
step, namely, to account by mechanical considerations for these stresses in the dielectric. I
therefore leave the theory at this point." Nothing in this file supplies such a mechanism; see
`Maxwell.Sources.art107_illustration`, `Maxwell.Sources.art110`, `Maxwell.Sources.art111`.

Editions. "1873 Art. 106/107" and "1881 Art. 106" are different articles: 1873 Art. 107
*supposes* the tension with equal lateral pressure ("we must assume … we must further suppose"),
while 1881 Art. 106 *derives* its type from the components (14). Each docstring names its edition.

Sign conventions. Maxwell's `∇²` is `−(d²/dx² + d²/dy² + d²/dz²)` (footnote to Art. 616,
vol. II, p. 235, "the negative sign is employed here in order to make our expressions consistent
with those in which Quaternions are employed"; the same sign in 1881 vol. I, Art. 103, eq. (3),
`∇²Ψ₂ = 4πρ₂` with `Ψ₂ = ∭ ρ₂/r` positive for positive charge), so his `∇²Ψ = 4πρ` is
`−ΔΨ = 4πρ` below.

Sources: Internet Archive `electricandmagne01maxwrich` (1873, vol. I) and
`treatiseonelectr01maxwrich` (1881, vol. I). The 1873 formula
typography is badly garbled in the OCR; the algebra was checked by re-deriving it. Art. 111's
displayed formula was read from Internet Archive `electricandmagne01maxwrich`, page n171 (vol. I, p. 134).
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

/-- Treatise 1873, vol. I, Art. 107 (p. 127), a supposition there: "a tension `p` at every point of the medium in the
direction of the resultant force `R` … in every direction perpendicular to `R` there is a
pressure `p`." As a stress along the unit direction `u`: `p (2 u_h u_k − δ_hk)` — Maxwell's own
decomposition at the end of 1873 Art. 106 (p. 126): "the tension `p` may be considered as a pressure
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
vol. II, p. 235; 1881 vol. I, Art. 103, eq. (3)). -/
noncomputable def maxwellNabla2 (Ψ : Vec3 → ℝ) (x : Vec3) : ℝ :=
  - ∑ i, pd i (fun y => pd i Ψ y) x

/-- The 1881 electrostatic stress from the potential (Treatise 1881, vol. I, Art. 105, eq. (14),
p. 147): `p_xx = (1/8π)((dΨ/dx)² − (dΨ/dy)² − (dΨ/dz)²)`, `p_xy = (1/4π)(dΨ/dx)(dΨ/dy)`, etc.
Maxwell's condition on reading these as a stress (Art. 105, p. 147, `Maxwell.Sources.art105_1881`):
if the action is direct action at a distance, they are "mere abbreviated forms for certain
symbolical expressions, and as having no physical significance"; only if the action "is kept up by
means of stress in the medium" are they a stress. Lean defines the matrix; the physical reading is
his hypothesis. -/
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

/-! ## 1881, Art. 105, integrated: the direct-action test on boxes -/

/-- The integral of the stress over the face `x_i = s` of the box `[a, b]` (the face is a box in
the other two coordinates), `k`-component. -/
noncomputable def faceIntegral (P : Vec3 → Stress) (a b : Vec3) (i : Fin 3) (s : ℝ) (k : Fin 3) :
    ℝ :=
  ∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), P (i.insertNth s y) i k

/-- The force exerted on the contents of the box `[a, b]` by the stress outside it, as a sum of
integrals of the stress over the six faces (outward normal `+e_i` on the face `x_i = b_i`, `−e_i`
on `x_i = a_i`; Art. 641 convention, `traction`). -/
noncomputable def boxSurfaceForce (P : Vec3 → Stress) (a b : Vec3) (k : Fin 3) : ℝ :=
  ∑ i, (faceIntegral P a b i (b i) k - faceIntegral P a b i (a i) k)

/-- A force density `f` "is accounted for by a distribution of stress `P`" on boxes: for every
box, the volume integral of `f` equals the surface integral of the stress over its boundary
(Treatise 1881, vol. I, Art. 105, eqs. (15)–(18), pp. 146–147). Maxwell asks this for *any*
closed surface separating the two systems; boxes are the case Mathlib's divergence theorem covers
today. -/
def AccountedForByStress (P : Vec3 → Stress) (f : Vec3 → Vec3) : Prop :=
  ∀ a b : Vec3, a ≤ b → ∀ k, ∫ x in Set.Icc a b, f x k = boxSurfaceForce P a b k

/-- Treatise 1881, vol. I, Arts. 104–105, pp. 145–147, and 1873, vol. I, Art. 108, p. 131 ("the
mechanical effect of these tensions and pressures on any portion of the medium, however bounded,
will be identical with the mechanical effect of the electrical forces according to the ordinary
theory"), on boxes: for a `C²` potential with `∇²Ψ = 4πρ` (Maxwell's sign) the force `ρE`,
`E = −∇Ψ`, is accounted for by the stress (14). Proved below as `art105_directAction`. -/
def Art105DirectAction : Prop :=
  ∀ (Ψ : Vec3 → ℝ) (ρ : Vec3 → ℝ), ContDiff ℝ 2 Ψ → (∀ x, maxwellNabla2 Ψ x = fourPi * ρ x) →
    AccountedForByStress (stress1881 Ψ) (fun x => ρ x • (-grad Ψ x))

theorem contDiff_grad_apply {Ψ : Vec3 → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (j : Fin 3) :
    ContDiff ℝ 1 (fun x => grad Ψ x j) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (m := 1) (by norm_num)
  exact h1.clm_apply contDiff_const

theorem contDiff_stress1881_apply {Ψ : Vec3 → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (h k : Fin 3) :
    ContDiff ℝ 1 (fun x => stress1881 Ψ x h k) := by
  have g := contDiff_grad_apply hΨ
  simp only [stress1881, componentForm, sq_eq]
  have := g 0; have := g 1; have := g 2; have := g h; have := g k
  fun_prop

/-- **Treatise 1881, vol. I, Art. 105, eqs. (15)–(18), pp. 146–147, on boxes.** For a `C²`
potential `Ψ` with `∇²Ψ = 4πρ` (Maxwell's sign, Art. 103 eq. (3)), on every box `[a, b]` the
volume integral of the force `ρE` equals the surface integral of the stress (14) over the six
faces. From the pointwise `art105_force` and
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`. Maxwell's "any closed surface"
is not covered; neither is the physical reading of the stress (`Maxwell.Sources.art105_1881`). -/
theorem art105_directAction : Art105DirectAction := by
  intro Ψ ρ hΨ hP a b hab k
  set f : Fin 3 → Vec3 → ℝ := fun i x => stress1881 Ψ x i k with hf
  have hfC : ∀ i, ContDiff ℝ 1 (f i) := fun i => contDiff_stress1881_apply hΨ i k
  have hpt : ∀ x, (ρ x • (-grad Ψ x)) k = ∑ i, fderiv ℝ (f i) x (Pi.single i 1) := by
    intro x
    have := congrFun (art105_force (hΨ.contDiffAt) (hP x)) k
    rw [← this]
    rfl
  simp_rw [hpt]
  have hcont : Continuous (fun x => ∑ i, fderiv ℝ (f i) x (Pi.single i 1)) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hfC i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  rw [MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable' a b hab f
    (fun i x => fderiv ℝ (f i) x) ∅ Set.countable_empty
    (fun i => (hfC i).continuous.continuousOn)
    (fun x _ i => ((hfC i).differentiable (by norm_num) x).hasFDerivAt)
    (hcont.integrableOn_Icc)]
  rfl

/-! ## 1881, Art. 106: the type of the stress -/

theorem componentForm_transpose (v : Vec3) : (componentForm v)ᵀ = componentForm v := by
  ext h k; simp [componentForm, δ, eq_comm]; ring

theorem traction_componentForm (v n : Vec3) :
    traction (componentForm v) n = (v ⬝ᵥ n / fourPi) • v - (sq v / (8 * Real.pi)) • n := by
  ext k
  simp only [traction, componentForm, Fin.sum_univ_three, δ, dotProduct, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  fin_cases k <;> simp <;> ring

/-- **Treatise 1881, vol. I, Art. 106, p. 148**, derived there from the components (14) (1873
Art. 107 instead *supposes* this tension): across an element whose
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
the same value with the sign reversed." Stated for a frame as Maxwell means it: `E ≠ 0`, and
`E, e₁, e₂` mutually perpendicular with `e₁, e₂` unit vectors. Then the stress is symmetric, `E`,
`e₁`, `e₂` are principal directions (each traction is along its own normal), and the principal
values are `E²/8π` along `E` and `−E²/8π` along `e₁` and `e₂`; the third value is the first with
the sign reversed, and it is nonzero. (The traction identities alone need only `E ⟂ e₁, e₂`.) -/
theorem art106_principal {E e₁ e₂ : Vec3} (hE : E ≠ 0) (h₁ : E ⬝ᵥ e₁ = 0) (h₂ : E ⬝ᵥ e₂ = 0)
    (h₁₂ : e₁ ⬝ᵥ e₂ = 0) (hu₁ : e₁ ⬝ᵥ e₁ = 1) (hu₂ : e₂ ⬝ᵥ e₂ = 1) :
    (componentForm E)ᵀ = componentForm E ∧
    traction (componentForm E) E = (sq E / (8 * Real.pi)) • E ∧
    traction (componentForm E) e₁ = (-(sq E / (8 * Real.pi))) • e₁ ∧
    traction (componentForm E) e₂ = (-(sq E / (8 * Real.pi))) • e₂ ∧
    e₁ ⬝ᵥ traction (componentForm E) e₂ = 0 ∧
    e₁ ⬝ᵥ traction (componentForm E) e₁ = -(sq E / (8 * Real.pi)) ∧
    e₂ ⬝ᵥ traction (componentForm E) e₂ = -(sq E / (8 * Real.pi)) ∧
    sq E / (8 * Real.pi) ≠ 0 := by
  have hsq : sq E ≠ 0 := by
    intro h
    exact hE (dotProduct_self_eq_zero.mp h)
  refine ⟨componentForm_transpose E, art106_tension E, by rw [art106_pressure h₁, neg_smul],
    by rw [art106_pressure h₂, neg_smul], ?_, ?_, ?_, ?_⟩
  · rw [art106_pressure h₂, dotProduct_smul, h₁₂, smul_eq_mul, mul_zero]
  · rw [art106_pressure h₁, dotProduct_smul, hu₁, smul_eq_mul, mul_one]
  · rw [art106_pressure h₂, dotProduct_smul, hu₂, smul_eq_mul, mul_one]
  · have : (8 * Real.pi) ≠ 0 := by simp [Real.pi_ne_zero]
    exact div_ne_zero hsq this

/-! ## 1873, Art. 111: energy per unit volume equals the tension per unit area -/

/-- **Treatise 1873, vol. I, Art. 111, p. 134.** "A dielectric medium, when thus polarized, is the
seat of electrical energy, and the energy in unit of volume of the medium is numerically equal
to the electric tension on unit of area, both quantities being equal to half the product of the
displacement and the resultant electromotive force, or
`p = ½ 𝔇 𝔈 = (1/8π) K 𝔈² = (2π/K) 𝔇²`,
where `p` is the electric tension, `𝔇` the displacement, `𝔈` the electromotive force, and `K`
the specific inductive capacity" (`Maxwell.Sources.art111_energy`; confirmed against the 1873 vol. I page scan,
p. 134, Internet Archive `electricandmagne01maxwrich`).

Here `R` is `𝔈` and `D = (K / 4π) • R` is `𝔇`. The printed juxtaposition `𝔇 𝔈` is the product
of the two magnitudes along the same line, written as the inner product. The third member needs
`K ≠ 0`. Arts. 107–108 carry no `K` (they use Art. 77, i.e. the `K = 1` case); that case is
the corollary `art107_tension_of_art111`,
not a disagreement with Art. 111. Art. 792 later uses this dielectric value. -/
theorem art111_energy_eq_tension (K : ℝ) (hK : K ≠ 0) (R : Vec3) :
    (1 / 2) * (((K / fourPi) • R) ⬝ᵥ R) = K * sq R / (8 * Real.pi) ∧
    (1 / 2) * (((K / fourPi) • R) ⬝ᵥ R) = (2 * Real.pi / K) * sq ((K / fourPi) • R) := by
  constructor <;> simp [sq, dotProduct_smul, fourPi] <;> field_simp [hK] <;> ring

/-- **Art. 107 as the `K = 1` case of Art. 111.** Arts. 107–108 carry no `K` (they use Art. 77,
i.e. the `K = 1` case), so Art. 111's `p = (1/8π) K 𝔈²` becomes `p = R²/8π`. -/
theorem art107_tension_of_art111 (R : Vec3) :
    (1 / 2) * (((1 / fourPi) • R) ⬝ᵥ R) = sq R / (8 * Real.pi) := by
  simpa using (art111_energy_eq_tension (K := 1) one_ne_zero R).1


/-! ## Art. 111 in a dielectric: the stress the tension belongs to

Art. 111 prints `p = ½ 𝔇 𝔈 = (1/8π) K 𝔈² = (2π/K) 𝔇²`; that is a *number*. The stress of a
dielectric of capacity `K` is `dielectricStress K E` below, whose tension along `E` is that number
for every `K`, and whose force is `(div 𝔇) • 𝔈` with `𝔇 = (K/4π) 𝔈`. Arts. 107–108 are the case
`K = 1` (`dielectricStress_one`, `componentForm`), which is the case Art. 77 gives (`4πρ = div E`).
-/

/-- **Art. 111's identity for every `K`.** The printed formula holds for `K = 0` as well, both
sides being `0` under Lean's total division, so `art111_energy_eq_tension`'s `K ≠ 0` is a
hypothesis about what the formula *means*, not about the identity. -/
theorem art111_energy_eq_tension_all (K : ℝ) (R : Vec3) :
    (1 / 2) * (((K / fourPi) • R) ⬝ᵥ R) = K * sq R / (8 * Real.pi) ∧
    (1 / 2) * (((K / fourPi) • R) ⬝ᵥ R) = (2 * Real.pi / K) * sq ((K / fourPi) • R) := by
  rcases eq_or_ne K 0 with hK | hK
  · subst hK; simp
  · exact art111_energy_eq_tension K hK R

/-- The electrostatic stress of a dielectric of capacity `K` (Art. 111): tension `p = K E²/8π`
along `E` with equal lateral pressure, `p_hk = K E_h E_k/4π − δ_hk K E²/8π`. -/
noncomputable def dielectricStress (K : ℝ) (E : Vec3) : Stress :=
  fun h k => K * (E h * E k) / fourPi - δ h k * (K * sq E) / (8 * Real.pi)

theorem dielectricStress_eq_smul (K : ℝ) (E : Vec3) :
    dielectricStress K E = K • componentForm E := by
  ext h k
  simp only [dielectricStress, componentForm, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `K = 1` is `componentForm`, the stress of Arts. 107–108. -/
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

theorem sq_smul_unit (r : ℝ) {u : Vec3} (hu : u ⬝ᵥ u = 1) : sq (r • u) = r ^ 2 := by
  simp only [sq, dotProduct_smul, smul_dotProduct, hu, smul_eq_mul, mul_one]
  ring

theorem differentiableAt_componentForm {F : Vec3 → Vec3} {x : Vec3}
    (hF : ∀ i, DifferentiableAt ℝ (fun y => F y i) x) (h k : Fin 3) :
    DifferentiableAt ℝ (fun y => componentForm (F y) h k) x := by
  simp only [componentForm, sq_eq]
  have := hF 0; have := hF 1; have := hF 2; have := hF h; have := hF k
  fun_prop

/-- **Art. 111 against Art. 107**, for every capacity: along `E = r u` the tension of
`dielectricStress K` is `½𝔇𝔈 = K r²/8π`, the energy per unit volume — the energy *is* the tension
on unit area, as Art. 111 asserts. -/
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

/-- **Across the field, for every capacity**: the pressure of `dielectricStress K` across a plane
at right angles to `E` is `K E²/8π`, of the same magnitude as the tension along `E`. -/
theorem dielectricStress_pressure {K : ℝ} {E n : Vec3} (hEn : E ⬝ᵥ n = 0) :
    traction (dielectricStress K E) n = -(K * sq E / (8 * Real.pi)) • n := by
  rw [dielectricStress_eq_smul, traction_smul, art106_pressure hEn]
  ext k
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- **Art. 107 from Art. 111, for every capacity `K`**: along `E = r u` a tension equal to the
energy per unit volume `½𝔇𝔈 = K r²/8π`, and across `E` a pressure of the same magnitude. -/
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

/-- **Art. 111's stress gives the force `(div 𝔇) • 𝔈`** for a curl-free electromotive intensity
and `𝔇 = (K/4π) • 𝔈`. With `K = 1` and `4πρ = div E` this is Art. 108's `ρ • E`. -/
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

/-- **`K = 1` recovers Art. 108's `art108_force`**, with the same `dielectricStress` object. -/
theorem dielectricStress_K_one_force {E : Vec3 → Vec3} {x : Vec3} {ρ : ℝ}
    (hE : ∀ i, DifferentiableAt ℝ (fun y => E y i) x) (hcurl : curl E x = 0)
    (h77 : div E x = fourPi * ρ) :
    stressForce (fun y => dielectricStress 1 (E y)) x = ρ • E x := by
  have hD : div (fun y => (1 / fourPi) • E y) x = ρ := by
    rw [div_const_smul (1 / fourPi) hE, h77]
    field_simp
  rw [art111_force_dielectric hE hcurl hD]

end Maxwell
