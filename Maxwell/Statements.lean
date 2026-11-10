/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.RadiationPressure
import Maxwell.Treatise.VectorPotential
import Maxwell.Treatise.GaugeLinearFunctional
import Maxwell.Treatise.ElectromotiveForce
import Maxwell.Sources
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Statements, and what is proved about them

The `Prop`s below are targets: claims of Maxwell's that should be provable, claims that need a
sharpened hypothesis to be true, or hypotheses of his. **None of them is assumed as an axiom.**
The root module `Maxwell` does not import this file.

Four things here *are* proved, about the statements themselves rather than in them:

* `art634_shape_needs_wire_hypothesis` — `Art634KineticEnergy` is refuted as stated: it relates two
  sides over independent data, so it needs the wire hypothesis ("the loops carry the current `J`").
* `art617Uniqueness_of_exists` — `Art617Uniqueness` follows from its existence half alone.
* `art616GaugeChoiceAvailable_of_poissonSolver` and `poisson_solvable_of_gaugeChoiceAvailable` —
  `Art616GaugeChoiceAvailable` is equivalent to one named lemma on the Poisson equation.
* the remaining statements carry the sharpest hypotheses their claims are known to need.

Maxwell's own stated limits (1873 Arts. 107, 110, 111, 645; 1865 §§ 73, 82; 1881 Art. 105) are not turned into statements of any
kind: there is no mathematical content to state, and they are kept verbatim in `Maxwell.Sources`.
-/

namespace Maxwell

open MeasureTheory Matrix

/-! ## 1881 Art. 105 / 1873 Art. 108: the direct-action test, integrated

The definitions `faceIntegral`, `boxSurfaceForce`, `AccountedForByStress`, `Art105DirectAction`
and the theorem `art105_directAction` now live in `Maxwell.Treatise.ElectrostaticStress` (proved,
on boxes). Maxwell's "any closed surface" remains wider than boxes and is not a separate
statement here. -/

/-! ## Energy: the integrations by parts of Arts. 631 and 635

The six definitions `Art631EnergyInField`, `Art635ElectrokineticInField`, `DecaysAsArt631`,
`Art631EnergyInFieldDecay`, `DecaysAsArt635`, `Art635ElectrokineticInFieldDecay` now live in
`Maxwell.Treatise.Energy`, with their proofs `art631_energyInField`, `art635_electrokineticInField`
(compact support) and `art631_energyInFieldDecay`, `art635_electrokineticInFieldDecay` (Maxwell's
decay rates; for Art. 635 with our `𝔄 ~ r⁻²`). The surface term is taken on the cubes
`[-n, n]³` (`integral_div_eq_zero_of_decay`). Equal totals only: no theorem here locates the
energy. -/

/-! ## Arts. 590 and 634: why 𝔄 is called a momentum (Lagrangian / generalized)

`Art590Impulse` now lives in `Maxwell.Treatise.ElectromotiveForce`, proved as `art590_impulse`
(fundamental theorem of calculus on `[0, ∞)`). -/

/-- **Shape of the Art. 634 claim.** Treatise 1873, vol. II, Art. 634, eq. (16), p. 248 (with
Art. 578): the kinetic energy of the currents, treated as velocities of a dynamical system
(Art. 604), is `T = ½ ∑ pᵢ iᵢ = ½ ∭ (Fu + Gv + Hw)`, with `pᵢ = ∮ 𝔄 · ds` the electromagnetic
momentum of circuit `i` (`circuitMomentum`). Lagrangian / generalized momentum, not a field
momentum density. The link between the circuits and `J` (that `J` is the current the circuits
carry) is not yet formalized, so this is the equation to be shown under that link, not yet a
closed target. -/
def Art634KineticEnergy {ι : Type} [Fintype ι] (A J : Vec3 → Vec3) (γ γ' : ι → ℝ → Vec3)
    (current : ι → ℝ) : Prop :=
  (1 / 2) * ∑ i, circuitMomentum A (γ i) (γ' i) * current i = (1 / 2) * ∫ x, A x ⬝ᵥ J x

/-! ## Art. 616: Maxwell's construction of `χ`, and Art. 617 uniqueness -/

/-- **Maxwell's construction (Art. 616, eqs. (5)–(7), p. 235), with later rigor for
existence and regularity.** Art. 616 does not merely suppose `χ = 0`. It constructs
`F′` as the potential of the current and `χ = (1/4π) ∭ J/r dx dy dz` (his `J = div 𝔄`,
eq. (2), not the current; this printed form of `χ` is the 1892 3rd edition's, per Grey's review,
and the 1873 first-edition formulas differ), then takes `F = F′ − dχ/dx`, so that `J` vanishes, and afterwards
"if we suppose it to be zero everywhere, `J` will also be zero everywhere." The proposition
below is the existence of some
`χ` making `div (𝔄 + ∇χ) = 0`; the general existence and regularity proof (beyond his integral
formula) is later analysis. The proved theorems `art616_induction_unchanged` and
`art616_circuitMomentum_unchanged` hold for any sufficiently smooth `χ`, which is more general
than his specific choice. `art616_gauge_iff_poisson` (`Maxwell.Treatise.VectorPotential`) proves
that the condition is exactly `∇²χ = J` (his sign); the open part is solving that Poisson
equation, which needs the Newtonian potential, not yet in Mathlib. Full gauge invariance of the
pair `(𝔄, Ψ)` is not his and is not stated. -/
def Art616GaugeChoiceAvailable : Prop :=
  ∀ A : Vec3 → Vec3, ContDiff ℝ ⊤ A → HasCompactSupport A →
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, div (fun y => A y + grad χ y) x = 0

/-- **Target (Art. 617, p. 236).** "When the distribution of electric currents is given, there
is one, and only one, distribution of the values of 𝔄, such that 𝔄 is everywhere finite and
continuous, and satisfies the equations `∇²𝔄 = 4πμC`, `S.∇𝔄 = 0`, and vanishes at an infinite
distance from the electric system." Maxwell's `∇²` (his sign) acts componentwise. The source
`C` (written in ASCII; a German letter in the Art. 618 table) is the total current whose
components are `u, v, w`, the same `u, v, w` as Art. 607 (E), so `4π C = curl H` and
`div C = 0`. (In the Art. 618 table `G` is a component of 𝔄, the Fraktur-G row is "the velocity
of a point", and the Fraktur-J row is "the intensity of magnetization".) Without the hypothesis
`div C = 0` the statement is false: if `μ ≠ 0` and `div C` is not identically zero, no decaying
solenoidal `𝔄` exists. The scalar `μ` is uniform: Art. 615 retains "the coefficient μ,
remembering that its value is unity in the electromagnetic system", and Art. 616 (p. 235):
"According to our hypothesis `a, b, c` are identical with `μα, μβ, μγ` respectively."
Existence is the construction of Art. 616 eqs. (5)–(7) (`𝔄 = μ ∭ C/r`; the 1873 printing of
Art. 617 has `1/μ` in front of the integral, which is inconsistent with `∇²𝔄 = 4πμC`);
uniqueness is Art. 617. Smoothness, compact support, and the precise function space are later
rigor.

Proved so far (`Maxwell.Treatise.VectorPotential`): `art617_difference` (two solutions differ by
a decaying harmonic, solenoidal field) and `art617_unique_of_liouville` (uniqueness, given a
Liouville statement for `ℝ³` that Mathlib does not yet have). Existence needs the Newtonian
potential, also not yet in Mathlib. The Prop stays open. -/
def Art617Uniqueness : Prop :=
  ∀ (μ : ℝ) (C : Vec3 → Vec3), ContDiff ℝ ⊤ C → HasCompactSupport C →
    (∀ x, div C x = 0) →
    ∃! A : Vec3 → Vec3,
      ContDiff ℝ 2 A ∧ (∀ x, div A x = 0) ∧
        (∀ i x, maxwellNabla2 (fun y => A y i) x = fourPi * μ * C x i) ∧
          Filter.Tendsto A (Filter.cocompact Vec3) (nhds (0 : Vec3))

/-! ## Magnetic matter: Art. 377 (empirical) versus Art. 644 (hypothesis) -/

/-- **Maxwell's empirical position**, Treatise 1873, vol. II, Art. 377, p. 4: "In every Magnet
the total quantity of Magnetism (reckoned algebraically) is zero." With Poisson's magnetic matter
of density `m` in the body occupying `body`. This is a statement about *totals*; Art. 644's
`AmpereWeber644` (`m = 0` everywhere) is a separate, stronger hypothesis, and neither supports a
theory of free magnetic charge (see also Art. 832, `Maxwell.Sources.art832`). -/
def TotalMagnetismZero377 (m : Vec3 → ℝ) (body : Set Vec3) : Prop :=
  ∫ x in body, m x = 0

/-! ## 1865 § 82: what the gravity analogy would require -/

/-- **The requirement Maxwell derived, not a theory he held.** Dynamical Theory 1865, § 82,
pp. 570–571 (Scientific Papers I): if gravitation acted through a medium as electrostatic action
does, but with like bodies attracting, the intrinsic energy per unit volume would be
`C − R²/8π` (eq. (47) as printed, Maxwell's units), so positivity of energy requires an enormous
undisturbed energy `C ≥ R²/8π` everywhere. He concludes: "I cannot go any further in this
direction in searching for the cause of gravitation" (`Maxwell.Sources.dyn1865_s82`). -/
def GravityMediumEnergyNonneg1865 (C : ℝ) (R : Vec3 → Vec3) : Prop :=
  ∀ x, 0 ≤ C - sq (R x) / (8 * Real.pi)
/-! ## Art. 634 as stated in `Maxwell.Statements` needs the wire hypothesis

`Maxwell.Statements.Art634KineticEnergy` relates two sides over *independent* data: the left side
depends only on `𝔄`, the loops `γᵢ` and the currents `iᵢ`; the right side only on `𝔄` and `J`.
Nothing in the statement says that `J` is the current distribution carried by the circuits `γᵢ`.
Without that link the equation is false, as the next theorem shows: a constant potential, zero
current density and a straight (open) path with unit current give `½` against `0`.

This is why Art. 634 cannot be closed from the hypotheses it is stated with: the missing
hypothesis is exactly "the loops `γᵢ` carry the current `J`", i.e. `J` is the (distributional)
sum `∑ iᵢ ∮_γᵢ δ`. -/

theorem axis_dot_axis_self (i : Fin 3) : axis i ⬝ᵥ axis i = 1 := by
  fin_cases i <;> simp [axis, dotProduct, Fin.sum_univ_three]

/-- **Art. 634's equation is refutable as stated.**  With `𝔄 = e₀` constant, the open path
`γ t = t e₀` and unit current, the momentum side is `½`, while with `J = 0` the current-density
side is `0`. -/
theorem art634_shape_needs_wire_hypothesis :
    ¬ Art634KineticEnergy (fun _ : Vec3 => axis 0) (fun _ => 0)
      (fun (_ : Unit) (t : ℝ) => t • axis 0) (fun (_ : Unit) (_ : ℝ) => axis 0)
      (fun (_ : Unit) => 1) := by
  have hcm : circuitMomentum (fun _ : Vec3 => axis 0) (fun t : ℝ => t • axis 0)
      (fun _ : ℝ => axis 0) = 1 := by
    simp [circuitMomentum, axis_dot_axis_self]
  intro h
  simp only [Art634KineticEnergy] at h
  have hJ : (∫ x : Vec3, (fun _ : Vec3 => axis 0) x ⬝ᵥ (fun _ => 0 : Vec3 → Vec3) x) = 0 := by
    simp
  rw [hJ, mul_zero] at h
  simp [hcm] at h


/-! ## Art. 617 uniqueness, given existence

`art617_solution_subsingleton` (`Maxwell.Treatise.VectorPotential`) makes uniqueness independent of
any smoothness of the current, so the open target reduces to constructing one solution. -/

/-- **`Art617Uniqueness` from the existence half alone.** Given, for every smooth compactly
supported solenoidal current `C`, one decaying solenoidal `𝔄` with `∇²𝔄 = 4πμC` componentwise, the
`∃!` of Art. 617 follows. -/
theorem art617Uniqueness_of_exists
    (hex : ∀ (μ : ℝ) (C : Vec3 → Vec3), ContDiff ℝ ⊤ C → HasCompactSupport C →
      (∀ x, div C x = 0) → ∃ A : Vec3 → Vec3,
        ContDiff ℝ 2 A ∧ (∀ x, div A x = 0) ∧
          (∀ i x, maxwellNabla2 (fun y => A y i) x = fourPi * μ * C x i) ∧
            Filter.Tendsto A (Filter.cocompact Vec3) (nhds (0 : Vec3))) :
    Art617Uniqueness := by
  intro μ C _ _ hdiv
  obtain ⟨A, hA⟩ := hex μ C ‹ContDiff ℝ ⊤ C› ‹HasCompactSupport C› hdiv
  exact ⟨A, hA, fun B hB => art617_solution_subsingleton μ C hB hA⟩


/-! ## Art. 616: the gauge choice is exactly Poisson solvability

`art616_gauge_iff_poisson` turned the gauge condition into `∇²χ = div 𝔄`. These two theorems turn
that into an equivalence of the open target with one named lemma on the Newtonian potential. -/

section Gauge

open Filter Topology in
/-- **Art. 616 reduced to the exact missing lemma.** If Poisson's equation `∇²χ = J` is solvable
for every smooth compactly supported `J` (the Newtonian potential), then Maxwell's gauge choice is
available for every smooth compactly supported `𝔄`. -/
theorem art616GaugeChoiceAvailable_of_poissonSolver (h : NewtonianPotentialSolver) :
    Art616GaugeChoiceAvailable := by
  intro A hA hAc
  obtain ⟨χ, hχ, hP⟩ := h (div A) (contDiff_div hA) (hasCompactSupport_div hAc)
  refine ⟨χ, hχ, ?_⟩
  exact (art616_gauge_iff_poisson
    (fun i => (contDiff_pi.1 hA i).differentiable (by simp)) hχ).mpr hP

/-- **The converse reduction.** If Maxwell's gauge choice is available (the target
`Art616GaugeChoiceAvailable`), then Poisson's equation `∇²χ = J` is solvable for every `J` that is
the divergence of a smooth compactly supported field. Together with
`art616GaugeChoiceAvailable_of_poissonSolver` this pins the open target exactly to Poisson
solvability on the image of `div`. -/
theorem poisson_solvable_of_gaugeChoiceAvailable (h : Art616GaugeChoiceAvailable)
    {A : Vec3 → Vec3} (hA : ContDiff ℝ ⊤ A) (hAc : HasCompactSupport A) :
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, maxwellNabla2 χ x = div A x := by
  obtain ⟨χ, hχ, h0⟩ := h A hA hAc
  exact ⟨χ, hχ, (art616_gauge_iff_poisson
    (fun i => (contDiff_pi.1 hA i).differentiable (by simp)) hχ).mp h0⟩


end Gauge

end Maxwell
