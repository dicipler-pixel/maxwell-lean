/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Basic
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
momentum of a closed circuit. Maxwell's *choice* `χ = 0` (`div 𝔄 = 0`) is a choice, and the full
later gauge transformation of the pair `(𝔄, Ψ)` is not his statement and is not formalized as his.

This is **not** a field momentum density (no `D × H/4πc`); see `Maxwell.Sources.art549` and
`Maxwell.Sources.art574_575` for his own caveats and null experiments.

Local source: `/workspace/maxwell_reread/n_electricandmagne02maxwrich.txt`.
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

end Maxwell
