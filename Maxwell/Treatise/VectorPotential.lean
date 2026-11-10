/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.ElectrostaticStress
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Electromagnetic momentum is the vector potential (Treatise 1873, vol. II, Arts. 590–591, 604, 616)

* **Art. 590 (pp. 214–215).** `𝔄 = (F, G, H)` "represents in direction and magnitude the
  time-integral of the electromotive force which a particle placed at the point `(x, y, z)` would
  experience if the primary current were suddenly stopped. We shall therefore call it the
  Electrokinetic Momentum at the point … It is identical with the quantity which we investigated
  in Art. 405 under the name of the vector-potential of magnetic induction." "The electrokinetic
  momentum of any finite line or circuit is the line-integral, extended along the line or
  circuit, of the resolved part of the electrokinetic momentum at each point of the same."
* **Art. 604 (p. 227).** The currents are treated as velocities of a dynamical system: this is
  momentum in the Lagrangian (generalized) sense. "The electromagnetic momentum of a circuit is the
  line-integral of `𝔄` round the circuit."
* **Art. 591, equations (A).** `a = dH/dy − dG/dz`, etc.: `𝔅 = curl 𝔄`.
* **Art. 598 (p. 221)** and **Art. 616 (p. 235).** The added terms `dΨ/dx` (Art. 598) and
  `dχ/dx` (Art. 616) "disappear from the integral when extended round the closed circuit";
  `χ` "disappears from the equations (A), and it is not related to any physical phenomenon. If we
  suppose it to be zero everywhere, `J` will also be zero everywhere" (`J = div 𝔄`).

What is proved is exactly that: a gradient added to `𝔄` changes neither `curl 𝔄` nor the
momentum of a closed circuit. The theorems hold for *any* `C²` (resp. differentiable) `χ`, which is
more general than Maxwell's: his `χ` is the specific function `χ = (1/4π)∭ J/r` built in Art. 616,
eqs. (5)–(7) (his `J = div 𝔄`, eq. (2), not the current).

"Momentum" here is in the Lagrangian (generalized) sense of Arts. 578, 604 and 634: the currents are
velocities of a dynamical system and `∮𝔄·ds` is the momentum conjugate to the current. `circuitMomentum`
is only the line-integral; its two defining properties: the
impulse of Art. 590 (`Art590Impulse`, proved as `art590_impulse` in
`Maxwell.Treatise.ElectromotiveForce`), and `T = ½∑ p i` of Art. 634 as the shape
of the claim (`Art634KineticEnergy`), not yet a closed target. Maxwell's *choice* `χ = 0`
(`div 𝔄 = 0`) is a choice, and the full
later gauge transformation of the pair `(𝔄, Ψ)` is not his statement and is not formalized as his.

This is **not** a field momentum density (no `D × H/4πc`); see `Maxwell.Sources.art549` and
`Maxwell.Sources.art574_575` for his own caveats and null experiments.

Source: Internet Archive `electricandmagne02maxwrich` (1873, vol. II).
-/

namespace Maxwell

open Matrix

/-- **Arts. 590, 604:** the electromagnetic (electrokinetic) momentum of a circuit
`γ : [0, 1] → space` with velocity `γ'`: `∫ (F dx/ds + G dy/ds + H dz/ds) ds`. -/
noncomputable def circuitMomentum (A : Vec3 → Vec3) (γ γ' : ℝ → Vec3) : ℝ :=
  ∫ t in (0 : ℝ)..1, A (γ t) ⬝ᵥ γ' t

/-- **Art. 591, equations (A):** the magnetic induction of the momentum, `𝔅 = curl 𝔄`. -/
noncomputable def inductionOf (A : Vec3 → Vec3) (x : Vec3) : Vec3 := curl A x

theorem fderiv_apply_eq_grad_dot {χ : Vec3 → ℝ} (p v : Vec3) :
    fderiv ℝ χ p v = grad χ p ⬝ᵥ v := by
  have hv : v = ∑ i, v i • axis i := by
    ext j; fin_cases j <;> simp [axis, Fin.sum_univ_three]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul, grad, pd, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Art. 616, p. 235:** "The quantity `χ` disappears from the equations (A)": adding the
gradient of a `C²` function to the electromagnetic momentum does not change the induction. -/
theorem art616_induction_unchanged {A : Vec3 → Vec3} {χ : Vec3 → ℝ} {x : Vec3}
    (hA : ∀ i, DifferentiableAt ℝ (fun y => A y i) x) (hχ : ContDiffAt ℝ 2 χ x) :
    inductionOf (fun y => A y + grad χ y) x = inductionOf A x := by
  have hd := differentiableAt_pd hχ
  ext i
  fin_cases i <;>
    simp only [inductionOf, curl, Pi.add_apply, grad] <;>
    simp [pd_add _ (hA _) (hd _), pd_pd_comm hχ]

/-- The line-integral of a gradient round a closed circuit vanishes. -/
theorem loop_integral_grad {χ : Vec3 → ℝ} {γ γ' : ℝ → Vec3}
    (hχ : ∀ p, DifferentiableAt ℝ χ p) (hγ : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt γ (γ' t) t)
    (hclosed : γ 0 = γ 1)
    (hint : IntervalIntegrable (fun t => grad χ (γ t) ⬝ᵥ γ' t) MeasureTheory.volume 0 1) :
    ∫ t in (0 : ℝ)..1, grad χ (γ t) ⬝ᵥ γ' t = 0 := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => χ (γ s)) (grad χ (γ t) ⬝ᵥ γ' t) t := by
    intro t ht
    have := (hχ (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t ht)
    rwa [fderiv_apply_eq_grad_dot] at this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, hclosed, sub_self]

/-- **Arts. 598 and 616:** the `χ` (or `Ψ`) terms "disappear from the integral when extended
round the closed circuit": the electromagnetic momentum of a closed circuit is unchanged when a
gradient is added to `𝔄`. -/
theorem art616_circuitMomentum_unchanged {A : Vec3 → Vec3} {χ : Vec3 → ℝ} {γ γ' : ℝ → Vec3}
    (hχ : ∀ p, DifferentiableAt ℝ χ p) (hγ : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt γ (γ' t) t)
    (hclosed : γ 0 = γ 1)
    (hintA : IntervalIntegrable (fun t => A (γ t) ⬝ᵥ γ' t) MeasureTheory.volume 0 1)
    (hintχ : IntervalIntegrable (fun t => grad χ (γ t) ⬝ᵥ γ' t) MeasureTheory.volume 0 1) :
    circuitMomentum (fun y => A y + grad χ y) γ γ' = circuitMomentum A γ γ' := by
  unfold circuitMomentum
  simp only [add_dotProduct]
  rw [intervalIntegral.integral_add hintA hintχ, loop_integral_grad hχ hγ hclosed hintχ, add_zero]

/-! ## Arts. 616–617: what is proved toward the gauge choice and uniqueness -/

section Art616617

open Filter Topology

/-- `div (𝔄 + ∇χ) = div 𝔄 − ∇²χ`, with Maxwell's `∇² = −Δ`. -/
theorem div_add_grad {A : Vec3 → Vec3} {χ : Vec3 → ℝ} {x : Vec3}
    (hA : ∀ i, DifferentiableAt ℝ (fun y => A y i) x) (hχ : ContDiffAt ℝ 2 χ x) :
    div (fun y => A y + grad χ y) x = div A x - maxwellNabla2 χ x := by
  simp only [div, maxwellNabla2, Pi.add_apply, grad,
    pd_add _ (hA _) (differentiableAt_pd hχ _), Finset.sum_add_distrib]
  ring

/-- **Art. 616 reduced to a Poisson equation.** A `C²` `χ` makes `𝔄 + ∇χ` solenoidal exactly when
`∇²χ = J` with Maxwell's `∇² = −Δ` and his `J = div 𝔄` (eq. (2); not the current). So
`Art616GaugeChoiceAvailable` is the solvability of this Poisson equation for compactly supported
smooth `J`, which needs the Newtonian potential `(1/4π)∭ J/r` (Euclidean `r`); Mathlib does not
yet provide it, and the Prop stays open. -/
theorem art616_gauge_iff_poisson {A : Vec3 → Vec3} {χ : Vec3 → ℝ}
    (hA : ∀ i, Differentiable ℝ (fun y => A y i)) (hχ : ContDiff ℝ 2 χ) :
    (∀ x, div (fun y => A y + grad χ y) x = 0) ↔ ∀ x, maxwellNabla2 χ x = div A x := by
  refine forall_congr' fun x => ?_
  rw [div_add_grad (fun i => hA i x) hχ.contDiffAt, sub_eq_zero, eq_comm]

theorem maxwellNabla2_sub {f g : Vec3 → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Vec3) :
    maxwellNabla2 (fun y => f y - g y) x = maxwellNabla2 f x - maxwellNabla2 g x := by
  have hfd : ∀ y, DifferentiableAt ℝ f y := fun y => hf.differentiable (by norm_num) y
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by norm_num) y
  have e : ∀ i, (fun y => pd i (fun z => f z - g z) y) = fun y => pd i f y - pd i g y :=
    fun i => funext fun y => pd_sub i (hfd y) (hgd y)
  simp only [maxwellNabla2, e, pd_sub _ (differentiableAt_pd hf.contDiffAt _)
    (differentiableAt_pd hg.contDiffAt _), Finset.sum_sub_distrib]
  ring

/-- **Art. 617, the difference of two solutions.** Two solutions of the Art. 617 system for the
same total current `C` (components `u, v, w`) differ by a `C²`, solenoidal field whose components
satisfy `∇² = 0` and vanish at infinity. -/
theorem art617_difference {μ : ℝ} {C A₁ A₂ : Vec3 → Vec3}
    (h₁ : ContDiff ℝ 2 A₁ ∧ (∀ x, div A₁ x = 0) ∧
      (∀ i x, maxwellNabla2 (fun y => A₁ y i) x = fourPi * μ * C x i) ∧
        Tendsto A₁ (cocompact Vec3) (𝓝 0))
    (h₂ : ContDiff ℝ 2 A₂ ∧ (∀ x, div A₂ x = 0) ∧
      (∀ i x, maxwellNabla2 (fun y => A₂ y i) x = fourPi * μ * C x i) ∧
        Tendsto A₂ (cocompact Vec3) (𝓝 0)) :
    ContDiff ℝ 2 (fun y => A₁ y - A₂ y) ∧ (∀ x, div (fun y => A₁ y - A₂ y) x = 0) ∧
      (∀ i x, maxwellNabla2 (fun y => (A₁ y - A₂ y) i) x = 0) ∧
        Tendsto (fun y => A₁ y - A₂ y) (cocompact Vec3) (𝓝 0) := by
  obtain ⟨c₁, d₁, p₁, t₁⟩ := h₁
  obtain ⟨c₂, d₂, p₂, t₂⟩ := h₂
  have hc₁ := contDiff_pi.1 c₁
  have hc₂ := contDiff_pi.1 c₂
  refine ⟨c₁.sub c₂, fun x => ?_, fun i x => ?_, by simpa using t₁.sub t₂⟩
  · rw [div_sub (fun i => (hc₁ i).differentiable (by norm_num) x)
      (fun i => (hc₂ i).differentiable (by norm_num) x), d₁, d₂, sub_zero]
  · simp only [Pi.sub_apply]
    rw [maxwellNabla2_sub (hc₁ i) (hc₂ i), p₁, p₂, sub_self]

/-- **Art. 617, uniqueness given Liouville.** If every `C²` harmonic function on space that
vanishes at infinity is zero (a Liouville / maximum-principle statement for `ℝ³`, not yet in
Mathlib), the Art. 617 solution is unique. The hypothesis `hL` is stated, not assumed globally. -/
theorem art617_unique_of_liouville
    (hL : ∀ u : Vec3 → ℝ, ContDiff ℝ 2 u → (∀ x, maxwellNabla2 u x = 0) →
      Tendsto u (cocompact Vec3) (𝓝 0) → u = 0)
    {μ : ℝ} {C A₁ A₂ : Vec3 → Vec3}
    (h₁ : ContDiff ℝ 2 A₁ ∧ (∀ x, div A₁ x = 0) ∧
      (∀ i x, maxwellNabla2 (fun y => A₁ y i) x = fourPi * μ * C x i) ∧
        Tendsto A₁ (cocompact Vec3) (𝓝 0))
    (h₂ : ContDiff ℝ 2 A₂ ∧ (∀ x, div A₂ x = 0) ∧
      (∀ i x, maxwellNabla2 (fun y => A₂ y i) x = fourPi * μ * C x i) ∧
        Tendsto A₂ (cocompact Vec3) (𝓝 0)) : A₁ = A₂ := by
  obtain ⟨c, -, p, t⟩ := art617_difference h₁ h₂
  funext x; ext i
  have := congrFun (hL (fun y => (A₁ y - A₂ y) i) (contDiff_pi.1 c i) (p i)
    (by simpa [Function.comp_def] using ((continuous_apply i).tendsto 0).comp t)) x
  simpa [sub_eq_zero] using this

end Art616617

section Liouville

open Filter Topology Set

/-! ## Art. 617: the Liouville step, and uniqueness of the vector potential

`art617_unique_of_liouville` above reduces Art. 617 to a Liouville-type theorem for `ℝ³`:

  every `C²` `u : Vec3 → ℝ` with `∇²u = 0` (Maxwell's sign, i.e. `Δu = 0`) that tends to `0` at
  infinity is `0`.

Mathlib has no maximum principle or mean value property for harmonic functions on `ℝⁿ` (its
`InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant` is for the complex plane), and
`Fin 3 → ℝ` carries no `InnerProductSpace` instance, so `Δ` is not available. The theorem is
proved here from the second-derivative test at an interior maximum, the weak maximum principle on
a ball, and a `+εy₀²` perturbation whose radius and size go to infinity and to zero. -/

theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {x : ℝ} (hg : ContDiff ℝ 2 g)
    (hx : IsLocalMax g x) : deriv (deriv g) x ≤ 0 := by
  rw [← not_lt]
  intro hL
  have hd1 : DifferentiableAt ℝ (deriv g) x :=
    ((hg.deriv' (n := 1)).differentiable (by norm_num)) x
  have h0 : deriv g x = 0 := hx.deriv_eq_zero
  have hslope : Tendsto (slope (deriv g) x) (𝓝[≠] x) (𝓝 (deriv (deriv g) x)) :=
    hd1.hasDerivAt.tendsto_slope
  have hev : ∀ᶠ y in 𝓝[≠] x, 0 < slope (deriv g) x y :=
    hslope.eventually (eventually_gt_nhds hL)
  obtain ⟨u, hu, husub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.1 hu
  obtain ⟨δ₂, hδ₂, hmax⟩ := Metric.mem_nhds_iff.1 hx
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = min δ₁ δ₂ := ⟨_, rfl⟩
  have hδ : 0 < δ := hδdef ▸ lt_min hδ₁ hδ₂
  have hδle₁ : δ ≤ δ₁ := hδdef ▸ min_le_left _ _
  have hδle₂ : δ ≤ δ₂ := hδdef ▸ min_le_right _ _
  have hpos : ∀ y, |y - x| < δ → y ≠ x → 0 < slope (deriv g) x y := by
    intro y hy hne
    refine husub ⟨hball ?_, hne⟩
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using lt_of_lt_of_le hy hδle₁
  set t : ℝ := x + δ / 2 with htdef
  have htx : |t - x| = δ / 2 := by
    rw [htdef]
    rw [show x + δ / 2 - x = δ / 2 by ring, abs_of_pos (by linarith)]
  have hhalfδ : δ / 2 < δ := by linarith
  have hxt : x < t := by rw [htdef]; linarith
  obtain ⟨c, hc, hcval⟩ := exists_deriv_eq_slope g hxt hg.continuous.continuousOn
    (hg.differentiable (by norm_num)).differentiableOn
  have hcx : 0 < c - x := sub_pos.mpr hc.1
  have hcdist : |c - x| < δ := by
    have h1 : c < t := hc.2
    rw [htdef] at h1
    rw [abs_of_pos hcx]
    linarith
  have hcne : c ≠ x := by linarith [hc.1]
  have hcpos : 0 < deriv g c / (c - x) := by
    have := hpos c hcdist hcne
    rwa [slope_def_field, h0, sub_zero] at this
  have hdpos : 0 < deriv g c := by
    have h1 : 0 < (deriv g c / (c - x)) * (c - x) := mul_pos hcpos hcx
    rwa [div_mul_cancel₀ _ (ne_of_gt hcx)] at h1
  have hgt : 0 < g t - g x := by
    have h2 : 0 < (g t - g x) / (t - x) := by rw [← hcval]; exact hdpos
    have h3 : 0 < ((g t - g x) / (t - x)) * (t - x) := mul_pos h2 (sub_pos.mpr hxt)
    rwa [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hxt))] at h3
  have hle : g t ≤ g x := by
    refine hmax ?_
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, htx] using lt_of_lt_of_le hhalfδ hδle₂
  linarith

/-- The line `t ↦ x + t • v`. -/
theorem hasDerivAt_line (x v : Vec3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add x

/-- First derivative of `t ↦ f (x + t • v)`. -/
theorem deriv_line {f : Vec3 → ℝ} (hf : ContDiff ℝ 2 f) (x v : Vec3) :
    deriv (fun t : ℝ => f (x + t • v)) = fun t => fderiv ℝ f (x + t • v) v := by
  funext t
  exact ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_line x v t)).deriv

/-- Second derivative of `t ↦ f (x + t • v)` at `0`. -/
theorem hasDerivAt_fderiv_line {f : Vec3 → ℝ} (hf : ContDiff ℝ 2 f) (x v : Vec3) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • v) v) (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    (differentiableAt_fderiv_of_contDiffAt hf.contDiffAt).hasFDerivAt
  have hcc : HasFDerivAt (fun y : Vec3 => fderiv ℝ f y v)
      ((fderiv ℝ (fderiv ℝ f) x).flip v) x := by
    simpa using hd.clm_apply (hasFDerivAt_const (x := x) (c := v))
  have hcc' : HasFDerivAt (fun y : Vec3 => fderiv ℝ f y v)
      ((fderiv ℝ (fderiv ℝ f) x).flip v) (x + (0:ℝ) • v) := by simpa using hcc
  exact hcc'.comp_hasDerivAt 0 (hasDerivAt_line x v 0)

/-- The second-derivative test at a local maximum, bilinear form version. -/
theorem second_deriv_nonpos_of_isLocalMax {f : Vec3 → ℝ} {x : Vec3} (hf : ContDiff ℝ 2 f)
    (hx : IsLocalMax f x) (v : Vec3) : fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  have hg : ContDiff ℝ 2 (fun t : ℝ => f (x + t • v)) := by
    apply hf.comp
    fun_prop
  have hx' : IsLocalMax (fun t : ℝ => f (x + t • v)) 0 := by
    have hcont : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    have hφ : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using hcont.tendsto 0
    have h := hφ.eventually hx
    simpa [IsLocalMax, IsMaxFilter] using h
  have hderiv2 : deriv (deriv (fun t : ℝ => f (x + t • v))) 0 = fderiv ℝ (fderiv ℝ f) x v v := by
    rw [deriv_line hf x v]
    exact (hasDerivAt_fderiv_line hf x v).deriv
  rw [← hderiv2]
  exact deriv_deriv_nonpos_of_isLocalMax hg hx'

/-- At an interior local maximum of a `C²` function, `maxwellNabla2 ≥ 0`. -/
theorem maxwellNabla2_nonneg_of_isLocalMax {f : Vec3 → ℝ} {x : Vec3} (hf : ContDiff ℝ 2 f)
    (hx : IsLocalMax f x) : 0 ≤ maxwellNabla2 f x := by
  have hsum : ∑ i : Fin 3, pd i (fun y => pd i f y) x ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    rw [pd_pd hf.contDiffAt]
    exact second_deriv_nonpos_of_isLocalMax hf hx (axis i)
  simp only [maxwellNabla2]
  linarith



/-! ### Additivity of `maxwellNabla2` (Maxwell's `∇² = −Δ` is linear) -/

theorem maxwellNabla2_add {f g : Vec3 → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : Vec3) :
    maxwellNabla2 (fun y => f y + g y) x = maxwellNabla2 f x + maxwellNabla2 g x := by
  have hfd : ∀ y, DifferentiableAt ℝ f y := fun y => hf.differentiable (by norm_num) y
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by norm_num) y
  have e : ∀ i, (fun y => pd i (fun z => f z + g z) y) = fun y => pd i f y + pd i g y :=
    fun i => funext fun y => pd_add i (hfd y) (hgd y)
  simp only [maxwellNabla2, e, pd_add _ (differentiableAt_pd hf.contDiffAt _)
    (differentiableAt_pd hg.contDiffAt _), Finset.sum_add_distrib]
  ring

theorem maxwellNabla2_const_mul (c : ℝ) {f : Vec3 → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec3) :
    maxwellNabla2 (fun y => c * f y) x = c * maxwellNabla2 f x := by
  have hfd : ∀ y, DifferentiableAt ℝ f y := fun y => hf.differentiable (by norm_num) y
  have hL : ∑ i, pd i (fun y => pd i (fun z => c * f z) y) x
      = c * ∑ i, pd i (fun y => pd i f y) x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (fun y => pd i (fun z => c * f z) y) = fun y => c * pd i f y from
      funext fun y => pd_const_mul i c (hfd y),
      pd_const_mul _ c (differentiableAt_pd hf.contDiffAt _)]
  simp only [maxwellNabla2, hL]
  ring

/-! ### `pd` of the coordinate functions and of `y ↦ y 0 * y 0` -/

theorem pd_coord (i j : Fin 3) (x : Vec3) : pd i (fun y : Vec3 => y j) x = if i = j then 1 else 0 := by
  rw [show (fun y : Vec3 => y j) = (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ) from rfl]
  simp [pd, axis, Pi.single_apply, eq_comm]

theorem pd_coord_sq (i : Fin 3) (x : Vec3) :
    pd i (fun y : Vec3 => y 0 * y 0) x = 2 * x 0 * (if i = 0 then 1 else 0) := by
  rw [pd_mul i (by fun_prop) (by fun_prop), pd_coord i 0]
  split <;> ring

theorem maxwellNabla2_coord_sq (x : Vec3) : maxwellNabla2 (fun y : Vec3 => y 0 * y 0) x = -2 := by
  have h0 : pd 0 (fun y : Vec3 => pd 0 (fun z : Vec3 => z 0 * z 0) y) x = 2 := by
    have h : (fun y : Vec3 => pd 0 (fun z : Vec3 => z 0 * z 0) y) = fun y => 2 * y 0 := by
      funext y
      rw [pd_coord_sq, if_pos rfl]
      ring
    rw [h, pd_const_mul _ 2 (by fun_prop), pd_coord]
    norm_num
  have h1 : pd 1 (fun y : Vec3 => pd 1 (fun z : Vec3 => z 0 * z 0) y) x = 0 := by
    have h : (fun y : Vec3 => pd 1 (fun z : Vec3 => z 0 * z 0) y) = fun _ => 0 := by
      funext y
      rw [pd_coord_sq, if_neg (by decide)]
      ring
    rw [h, pd_const]
  have h2 : pd 2 (fun y : Vec3 => pd 2 (fun z : Vec3 => z 0 * z 0) y) x = 0 := by
    have h : (fun y : Vec3 => pd 2 (fun z : Vec3 => z 0 * z 0) y) = fun _ => 0 := by
      funext y
      rw [pd_coord_sq, if_neg (by decide)]
      ring
    rw [h, pd_const]
  simp only [maxwellNabla2, Fin.sum_univ_three, h0, h1, h2]
  norm_num

theorem maxwellNabla2_neg_coord_sq (x : Vec3) :
    maxwellNabla2 (fun y : Vec3 => -(y 0 * y 0)) x = 2 := by
  have h : (fun y : Vec3 => -(y 0 * y 0)) = fun y => (-1 : ℝ) * (y 0 * y 0) := by
    funext y; ring
  rw [h, maxwellNabla2_const_mul]
  · rw [maxwellNabla2_coord_sq]; norm_num
  · fun_prop

/-- The hypothesis of the maximum principle is satisfiable (`f = y₀²`, `∇²f = −2`), so
`exists_max_on_sphere` is not vacuous. -/
theorem exists_maxwellNabla2_neg : ∃ f : Vec3 → ℝ, ContDiff ℝ 2 f ∧ ∀ z, maxwellNabla2 f z < 0 :=
  ⟨fun y => y 0 * y 0, by fun_prop, fun z => by rw [maxwellNabla2_coord_sq]; norm_num⟩

/-! ### The weak maximum principle on a ball

The sign convention: `maxwellNabla2 = −Δ`, so `maxwellNabla2 f < 0` is `Δf > 0`, the strictly
*subharmonic* case, in which an interior maximum is impossible. -/

/-- **Weak maximum principle**: if `∇²f < 0` on the open ball of radius `R`, then every interior
value of `f` is dominated by some value on the sphere of radius `R`. -/
theorem exists_max_on_sphere {f : Vec3 → ℝ} {R : ℝ} (hf : ContDiff ℝ 2 f) (hR : 0 < R)
    (hneg : ∀ z : Vec3, ‖z‖ < R → maxwellNabla2 f z < 0) (x : Vec3) (hx : ‖x‖ < R) :
    ∃ y : Vec3, ‖y‖ = R ∧ f x ≤ f y := by
  have hne : (Metric.closedBall (0 : Vec3) R).Nonempty := ⟨0, Metric.mem_closedBall_self hR.le⟩
  obtain ⟨y, hy, hymax⟩ := (isCompact_closedBall (0 : Vec3) R).exists_isMaxOn hne
    hf.continuous.continuousOn
  have hyball : ‖y‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hy
  have hyR : ‖y‖ = R := by
    rcases lt_or_eq_of_le hyball with hlt | heq
    · -- an interior maximizer would be a local maximum, where `∇²f ≥ 0`
      exfalso
      have hnhds : Metric.closedBall (0 : Vec3) R ∈ 𝓝 y := by
        refine Filter.mem_of_superset (Metric.ball_mem_nhds y (by linarith : 0 < R - ‖y‖)) ?_
        intro z hz
        simp only [Metric.mem_closedBall, dist_zero_right]
        have hzy : dist z y < R - ‖y‖ := by simpa [Metric.mem_ball] using hz
        have h1 : ‖z‖ = ‖y + (z - y)‖ := by rw [add_sub_cancel]
        rw [h1]
        have h2 : ‖y + (z - y)‖ ≤ ‖y‖ + ‖z - y‖ := norm_add_le _ _
        have h3 : ‖z - y‖ = dist z y := by rw [dist_eq_norm]
        linarith
      have hloc : IsLocalMax f y := Filter.mem_of_superset hnhds hymax
      have h1 := maxwellNabla2_nonneg_of_isLocalMax hf hloc
      have h2 := hneg y hlt
      linarith
    · exact heq
  refine ⟨y, hyR, hymax ?_⟩
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt hx

/-- `∇²` of the perturbation `y ↦ u y + ε y₀²`: it lowers `∇²` by `2ε` (i.e. raises `Δ`). -/
theorem maxwellNabla2_perturb {u : Vec3 → ℝ} (hu : ContDiff ℝ 2 u) (ε : ℝ) (z : Vec3) :
    maxwellNabla2 (fun y : Vec3 => u y + ε * (y 0 * y 0)) z = maxwellNabla2 u z - 2 * ε := by
  rw [maxwellNabla2_add hu (by fun_prop : ContDiff ℝ 2 (fun y : Vec3 => ε * (y 0 * y 0))),
    maxwellNabla2_const_mul]
  · rw [maxwellNabla2_coord_sq]; ring
  · fun_prop

/-! ### Liouville for Maxwell's `∇²` -/

/-- A `C²` function with `∇²f = 0` everywhere that tends to `0` at infinity is `≤ 0`: the maximum
principle on balls, with the radius tending to infinity and the perturbation switched off first. -/
theorem le_zero_of_maxwellNabla2_eq_zero {u : Vec3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hbar : ∀ x, maxwellNabla2 u x = 0) (hdec : Tendsto u (cocompact Vec3) (𝓝 0)) :
    ∀ x, u x ≤ 0 := by
  intro x₀
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- the decay gives a sphere of radius `R > ‖x₀‖` on which `u < δ/2`
  obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact.1
    (hdec.eventually (Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0:ℝ) < δ / 2)))
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt ‖x₀‖ (0 : Vec3)
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg x₀) hR
  -- the perturbation is chosen after `R`, small enough that `ε R² ≤ δ/2`
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = δ / (4 * (1 + R ^ 2)) := ⟨_, rfl⟩
  have hden : 0 < 1 + R ^ 2 := by positivity
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hcost : ε * R ^ 2 ≤ δ / 2 := by
    have h4 : ε * R ^ 2 ≤ ε * (1 + R ^ 2) := by nlinarith
    have h5 : ε * (1 + R ^ 2) = δ / 4 := by rw [hεdef]; field_simp
    linarith
  have hfC : ContDiff ℝ 2 (fun y : Vec3 => u y + ε * (y 0 * y 0)) := by fun_prop
  have hfneg : ∀ z : Vec3, ‖z‖ < R →
      maxwellNabla2 (fun y : Vec3 => u y + ε * (y 0 * y 0)) z < 0 := by
    intro z _
    rw [maxwellNabla2_perturb hu ε z, hbar, zero_sub]
    linarith
  obtain ⟨y, hyR, hle⟩ := exists_max_on_sphere hfC hRpos hfneg x₀ hR
  -- `y` lies outside `K`, where `u` is small
  have hyK : y ∉ K := by
    intro hy
    have h1 := hKR hy
    rw [Metric.mem_ball, dist_zero_right] at h1
    linarith
  have huy : u y < δ / 2 := by
    have h1 := hKsub hyK
    have h2 : dist (u y) 0 < δ / 2 := h1
    rw [Real.dist_eq, sub_zero, abs_lt] at h2
    exact h2.2
  have hx2 : 0 ≤ ε * (x₀ 0 * x₀ 0) := mul_nonneg hε.le (mul_self_nonneg _)
  have hy2 : (y 0) * (y 0) ≤ R ^ 2 := by
    have h1 : |y 0| ≤ R := by
      have h2 : |y 0| ≤ ‖y‖ := norm_le_pi_norm y 0
      rw [hyR] at h2
      exact h2
    nlinarith [abs_nonneg (y 0), sq_abs (y 0)]
  have hy3 : ε * (y 0 * y 0) ≤ ε * R ^ 2 := mul_le_mul_of_nonneg_left hy2 hε.le
  linarith

/-- **Liouville's theorem for Maxwell's `∇²` on `ℝ³`.** A `C²` function with `∇²u = 0` everywhere
that tends to `0` at infinity is identically zero. (This is exactly the hypothesis `hL` of
`Maxwell.art617_unique_of_liouville`.) -/
theorem eq_zero_of_maxwellNabla2_eq_zero {u : Vec3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hbar : ∀ x, maxwellNabla2 u x = 0) (hdec : Tendsto u (cocompact Vec3) (𝓝 0)) : u = 0 := by
  funext x₀
  have h1 : u x₀ ≤ 0 := le_zero_of_maxwellNabla2_eq_zero hu hbar hdec x₀
  have h2 : -u x₀ ≤ 0 := by
    refine le_zero_of_maxwellNabla2_eq_zero hu.neg ?_ ?_ x₀
    · intro x
      have hneg : (fun y : Vec3 => -u y) = fun y => (-1 : ℝ) * u y := by
        funext y; ring
      rw [hneg, maxwellNabla2_const_mul _ hu, hbar]
      ring
    · simpa using hdec.neg
  have h2' : -(u x₀) ≤ 0 := h2
  simp only [Pi.zero_apply]
  linarith

/-- The Liouville statement in the exact form taken as a hypothesis by
`Maxwell.art617_unique_of_liouville`. -/
theorem liouville_maxwellNabla2 :
    ∀ u : Vec3 → ℝ, ContDiff ℝ 2 u → (∀ x, maxwellNabla2 u x = 0) →
      Tendsto u (cocompact Vec3) (𝓝 0) → u = 0 :=
  fun _ hu hb hd => eq_zero_of_maxwellNabla2_eq_zero hu hb hd

/-! ### Sharpness: a `∇²`-harmonic function that does not tend to `0`

The decay hypothesis in the Liouville theorem is essential, not a convenience: the coordinate
functions are `∇²`-harmonic and do not tend to `0` at infinity. -/

theorem maxwellNabla2_coord (x : Vec3) : maxwellNabla2 (fun y : Vec3 => y 0) x = 0 := by
  have h0 : pd 0 (fun y : Vec3 => pd 0 (fun z : Vec3 => z 0) y) x = 0 := by
    have h : (fun y : Vec3 => pd 0 (fun z : Vec3 => z 0) y) = fun _ => 1 := by
      funext y; rw [pd_coord, if_pos rfl]
    rw [h, pd_const]
  have h1 : pd 1 (fun y : Vec3 => pd 1 (fun z : Vec3 => z 0) y) x = 0 := by
    have h : (fun y : Vec3 => pd 1 (fun z : Vec3 => z 0) y) = fun _ => 0 := by
      funext y; rw [pd_coord, if_neg (by decide)]
    rw [h, pd_const]
  have h2 : pd 2 (fun y : Vec3 => pd 2 (fun z : Vec3 => z 0) y) x = 0 := by
    have h : (fun y : Vec3 => pd 2 (fun z : Vec3 => z 0) y) = fun _ => 0 := by
      funext y; rw [pd_coord, if_neg (by decide)]
    rw [h, pd_const]
  simp only [maxwellNabla2, Fin.sum_univ_three, h0, h1, h2]
  norm_num

theorem not_tendsto_coord : ¬ Tendsto (fun y : Vec3 => y 0) (cocompact Vec3) (𝓝 0) := by
  intro h
  obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact.1
    (h.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos))
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt (0 : ℝ) (0 : Vec3)
  set t : ℝ := R + 1 with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  set pt : Vec3 := fun i : Fin 3 => if i = 0 then t else 0 with hpt
  have hpt0 : pt 0 = t := by simp [hpt]
  have hnotK : pt ∉ K := by
    intro hmem
    have h1 := hKR hmem
    rw [Metric.mem_ball, dist_zero_right] at h1
    have h2 : |pt 0| ≤ ‖pt‖ := norm_le_pi_norm pt 0
    rw [hpt0] at h2
    have h3 : |t| = t := abs_of_pos (by linarith)
    rw [h3] at h2
    linarith
  have hsmall := hKsub hnotK
  have h4 : dist (pt 0) 0 < 1 := hsmall
  rw [Real.dist_eq, hpt0, sub_zero, abs_of_pos (by linarith)] at h4
  linarith

/-! ### Art. 617: uniqueness of the vector potential -/

/-- **Art. 617 (Treatise 1873, vol. II, p. 236), uniqueness half**: for a given `μ` and current
`C`, there is at most one `C²`, solenoidal, decaying `𝔄` with `∇²𝔄 = 4πμC` componentwise. -/
theorem art617_uniqueness {μ : ℝ} {C A₁ A₂ : Vec3 → Vec3}
    (h₁ : ContDiff ℝ 2 A₁ ∧ (∀ x, div A₁ x = 0) ∧
      (∀ i x, maxwellNabla2 (fun y => A₁ y i) x = fourPi * μ * C x i) ∧
        Tendsto A₁ (cocompact Vec3) (𝓝 0))
    (h₂ : ContDiff ℝ 2 A₂ ∧ (∀ x, div A₂ x = 0) ∧
      (∀ i x, maxwellNabla2 (fun y => A₂ y i) x = fourPi * μ * C x i) ∧
        Tendsto A₂ (cocompact Vec3) (𝓝 0)) : A₁ = A₂ :=
  art617_unique_of_liouville liouville_maxwellNabla2 h₁ h₂

/-- The solutions of the Art. 617 system form a subsingleton — in particular this needs **no**
hypothesis on `C` (not `ContDiff`, not compact support, not `div C = 0`). -/
theorem art617_solution_subsingleton (μ : ℝ) (C : Vec3 → Vec3) :
    {A : Vec3 → Vec3 | ContDiff ℝ 2 A ∧ (∀ x, div A x = 0) ∧
      (∀ i x, maxwellNabla2 (fun y => A y i) x = fourPi * μ * C x i) ∧
        Tendsto A (cocompact Vec3) (𝓝 0)}.Subsingleton := by
  intro A₁ h₁ A₂ h₂
  exact art617_uniqueness h₁ h₂

/-- **Art. 617 with `μ = 0`**: the full `∃!` statement, with the unique solution `𝔄 = 0`. This is
the case of the `∃!` form in `Maxwell.Statements.Art617Uniqueness` that needs no Newtonian
potential; for `μ ≠ 0` only uniqueness is proved here. -/
theorem art617_existsUnique_zero (C : Vec3 → Vec3) :
    ∃! A : Vec3 → Vec3,
      ContDiff ℝ 2 A ∧ (∀ x, div A x = 0) ∧
        (∀ i x, maxwellNabla2 (fun y => A y i) x = fourPi * 0 * C x i) ∧
          Tendsto A (cocompact Vec3) (𝓝 0) := by
  have h0 : ContDiff ℝ 2 (0 : Vec3 → Vec3) ∧ (∀ x, div (0 : Vec3 → Vec3) x = 0) ∧
      (∀ i x, maxwellNabla2 (fun y => (0 : Vec3 → Vec3) y i) x = fourPi * 0 * C x i) ∧
        Tendsto (0 : Vec3 → Vec3) (cocompact Vec3) (𝓝 0) := by
    refine ⟨contDiff_const, ?_, ?_, tendsto_const_nhds⟩
    · intro x; simp [div, pd_const]
    · intro i x; simp [maxwellNabla2, pd_const]
  exact ⟨0, h0, fun A hA => art617_solution_subsingleton 0 C hA h0⟩

end Liouville

end Maxwell
