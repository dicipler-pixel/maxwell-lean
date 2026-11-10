/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.ElectrostaticStress
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

end Maxwell
