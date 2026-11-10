/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.RadiationPressure
import Maxwell.Treatise.VectorPotential
import Maxwell.Treatise.ElectromotiveForce
import Maxwell.Sources
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Statements only

Everything in this file is a `Prop` (a statement) or a definition used to write one. **Nothing
here is proved, and nothing here is assumed as an axiom.** The root module `Maxwell` does not
import this file. Each statement says whether it is a claim of Maxwell's that should be provable
(a target), one that needs a sharpened hypothesis to be true, or a hypothesis of his.

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

/-! ## Energy: the integrations by parts of Arts. 631 and 635 -/

/-- **Target (expected provable, with a sharpened hypothesis).** Treatise 1873, vol. II,
Arts. 630–631, pp. 246–247: `W = ½ ∑ eΨ`, with the quantity of electricity in an element
`(df/dx + dg/dy + dh/dz) dx dy dz`, equals `½ ∭ (Pf + Qg + Rh) dx dy dz` over all space.
Maxwell uses decay at infinity (`Ψ ~ r⁻¹`, `D ~ r⁻²`); the statement uses compact support,
which is stronger and excludes every case he treats (any system with net charge has `Ψ ~ r⁻¹`).
A `C¹` `D` also excludes the conductor surface charges of Art. 630's `½∑ eΨ`. Keep this as a
stepping stone; `Art631EnergyInFieldDecay` is the claim with his decay rates.

Equality of the two totals is all the mathematics gives, and it is all Art. 631 claims: "the
electrostatic energy of the whole field will be the same *if we suppose* that it resides…"
(`Maxwell.Sources.art631`). It does **not** locate the energy. Location is the physical claim of
1865, § 74 (`Maxwell.Sources.dyn1865_s74`), of Art. 636 as a hypothesis, and of 1873 Art. 111
("is the seat of electrical energy", `Maxwell.Sources.art111_energy`). -/
def Art631EnergyInField : Prop :=
  ∀ (Ψ : Vec3 → ℝ) (D : Vec3 → Vec3), ContDiff ℝ 1 Ψ → ContDiff ℝ 1 D →
    HasCompactSupport Ψ → HasCompactSupport D →
    (1 / 2) * ∫ x, div D x * Ψ x = ∫ x, electrostaticEnergy631 (-grad Ψ x) (D x)

/-- **Target (expected provable, with a sharpened hypothesis).** Treatise 1873, vol. II,
Arts. 634–635, eqs. (16)–(19), pp. 248–249: `T = ½ ∭ (Fu + Gv + Hw)` over the currents equals
`(1/8π) ∭ (aα + bβ + cγ)` over all space, with `𝔅 = curl 𝔄` (Art. 591) and `4πJ = curl H`
(Art. 607). Compact support replaces Maxwell's decay `H ~ r⁻³` and excludes every case he treats.
Keep this as a stepping stone; `Art635ElectrokineticInFieldDecay` is the claim with his decay
rates. Again: equal totals, not a proof of where the energy is (location of the kinetic energy
is the hypothesis of Art. 636, `Maxwell.Sources.art636`, and of 1865 § 74). -/
def Art635ElectrokineticInField : Prop :=
  ∀ (A H : Vec3 → Vec3), ContDiff ℝ 1 A → ContDiff ℝ 1 H →
    HasCompactSupport A → HasCompactSupport H →
    (1 / 2) * ∫ x, A x ⬝ᵥ ((1 / fourPi) • curl H x) =
      ∫ x, electrokineticEnergy636 (curl A x) (H x)

/-- Maxwell's decay in Art. 631: `Ψ` of the order `r⁻¹`, and `f, g, h` (the components of `D`)
of the order `r⁻²`, for large `r`. (`‖x‖` on `Fin 3 → ℝ` is equivalent to Euclidean `r`.) -/
def DecaysAsArt631 (Ψ : Vec3 → ℝ) (D : Vec3 → Vec3) : Prop :=
  ∃ CΨ CD : ℝ, ∀ x : Vec3, x ≠ 0 →
    |Ψ x| ≤ CΨ / ‖x‖ ∧ ∀ i, |D x i| ≤ CD / ‖x‖ ^ 2

/-- **Target (his claim).** The same equality as `Art631EnergyInField`, under Maxwell's decay
`Ψ ~ r⁻¹`, `D ~ r⁻²` (Art. 631) and integrability, rather than compact support. A `C¹` `D`
still excludes Art. 630's surface charges. -/
def Art631EnergyInFieldDecay : Prop :=
  ∀ (Ψ : Vec3 → ℝ) (D : Vec3 → Vec3), ContDiff ℝ 1 Ψ → ContDiff ℝ 1 D →
    DecaysAsArt631 Ψ D →
    Integrable (fun x => div D x * Ψ x) →
    Integrable (fun x => electrostaticEnergy631 (-grad Ψ x) (D x)) →
    (1 / 2) * ∫ x, div D x * Ψ x = ∫ x, electrostaticEnergy631 (-grad Ψ x) (D x)

/-- Maxwell prints, in Art. 635 (p. 248), that `α, β, γ` (the components of `H`) are of the
order of magnitude `r⁻³`. The companion decay `𝔄 ~ r⁻²` is ours (needed for the boundary
term, and natural for closed currents), not a rate he prints there. -/
def DecaysAsArt635 (A H : Vec3 → Vec3) : Prop :=
  ∃ CA CH : ℝ, ∀ x : Vec3, x ≠ 0 →
    (∀ i, |A x i| ≤ CA / ‖x‖ ^ 2) ∧ ∀ i, |H x i| ≤ CH / ‖x‖ ^ 3

/-- **Target (his claim, plus our decay of 𝔄).** The same equality as
`Art635ElectrokineticInField`, under Maxwell's decay `H ~ r⁻³` (Art. 635) and our `A ~ r⁻²`,
with integrability, rather than compact support. -/
def Art635ElectrokineticInFieldDecay : Prop :=
  ∀ (A H : Vec3 → Vec3), ContDiff ℝ 1 A → ContDiff ℝ 1 H →
    DecaysAsArt635 A H →
    Integrable (fun x => A x ⬝ᵥ ((1 / fourPi) • curl H x)) →
    Integrable (fun x => electrokineticEnergy636 (curl A x) (H x)) →
    (1 / 2) * ∫ x, A x ⬝ᵥ ((1 / fourPi) • curl H x) =
      ∫ x, electrokineticEnergy636 (curl A x) (H x)

/-! ## Arts. 590 and 634: why 𝔄 is called a momentum (Lagrangian / generalized) -/

/-- **Target.** Treatise 1873, vol. II, Art. 590, p. 214: 𝔄 "represents in direction and
magnitude the time-integral of the electromotive force which a particle placed at the point
`(x, y, z)` would experience if the primary current were suddenly stopped." For a body at rest
(`velocity = 0`) with `Ψ = 0`, `∫₀^∞ emf598 0 B (∂ₜ𝔄) 0 dt = 𝔄(0)` when `𝔄 → 0` as
`t → ∞`. This is Lagrangian / generalized momentum (Art. 604), not a field momentum density. -/
def Art590Impulse : Prop :=
  ∀ (A : ℝ → Vec3) (B : Vec3),
    (∀ t, DifferentiableAt ℝ A t) →
    Filter.Tendsto A Filter.atTop (nhds (0 : Vec3)) →
    IntegrableOn (fun t => emf598 0 B (deriv A t) 0) (Set.Ici (0 : ℝ)) →
      ∫ t in Set.Ici (0 : ℝ), emf598 0 B (deriv A t) 0 = A 0

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
eq. (2), not the current), then takes `F = F′ − dχ/dx`, so that `J` vanishes, and afterwards
"if we suppose it to be zero everywhere, `J` will also be zero everywhere." The proposition
below is the existence of some
`χ` making `div (𝔄 + ∇χ) = 0`; the general existence and regularity proof (beyond his integral
formula) is later analysis. The proved theorems `art616_induction_unchanged` and
`art616_circuitMomentum_unchanged` hold for any sufficiently smooth `χ`, which is more general
than his specific choice. Full gauge invariance of the pair `(𝔄, Ψ)` is not his and is not
stated. -/
def Art616GaugeChoiceAvailable : Prop :=
  ∀ A : Vec3 → Vec3, ContDiff ℝ ⊤ A → HasCompactSupport A →
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, div (fun y => A y + grad χ y) x = 0

/-- **Target (Art. 617, p. 236).** "When the distribution of electric currents is given, there
is one, and only one, distribution of the values of 𝔄, such that 𝔄 is everywhere finite and
continuous, and satisfies the equations `∇²𝔄 = 4πμ𝔊`, `S.∇𝔄 = 0`, and vanishes at an infinite
distance from the electric system." Maxwell's `∇²` (his sign) acts componentwise. The source
`𝔊` is the total current (Art. 618 table), which is solenoidal by Art. 607 (E)
(`4π𝔊 = curl H`, so `div 𝔊 = 0`). Without that hypothesis the statement is false: if `μ ≠ 0`
and `div G` is not identically zero, no decaying solenoidal `𝔄` exists. The scalar `μ` is
uniform: "According to our hypothesis `a, b, c` are identical with `μα, μβ, μγ` respectively"
(Art. 616, p. 235). Existence is the construction of Art. 616 eqs. (5)–(7); uniqueness is
Art. 617. Smoothness, compact support, and the precise function space are later rigor. -/
def Art617Uniqueness : Prop :=
  ∀ (μ : ℝ) (G : Vec3 → Vec3), ContDiff ℝ ⊤ G → HasCompactSupport G →
    (∀ x, div G x = 0) →
    ∃! A : Vec3 → Vec3,
      ContDiff ℝ 2 A ∧ (∀ x, div A x = 0) ∧
        (∀ i x, maxwellNabla2 (fun y => A y i) x = fourPi * μ * G x i) ∧
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

end Maxwell
