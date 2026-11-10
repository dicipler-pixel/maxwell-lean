/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.RadiationPressure
import Maxwell.Treatise.VectorPotential
import Maxwell.Sources
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Statements only

Everything in this file is a `Prop` (a statement) or a definition used to write one. **Nothing
here is proved, and nothing here is assumed as an axiom.** The root module `Maxwell` does not
import this file. Each statement says whether it is a claim of Maxwell's that should be provable
(a target), one that needs a sharpened hypothesis to be true, or a hypothesis of his.

Maxwell's own stated limits (Arts. 111, 645; 1865 § 82) are not turned into statements of any
kind: there is no mathematical content to state, and they are kept verbatim in `Maxwell.Sources`.
-/

namespace Maxwell

open MeasureTheory Matrix

/-! ## 1881 Art. 105 / 1873 Art. 108: the direct-action test, integrated -/

/-- The force exerted on the contents of the box `[a, b]` by the stress outside it, as a sum of
integrals of the stress over the six faces (outward normal `+e_i` on the face `x_i = b_i`, `−e_i`
on `x_i = a_i`). -/
noncomputable def faceIntegral (P : Vec3 → Stress) (a b : Vec3) (i : Fin 3) (s : ℝ) (k : Fin 3) :
    ℝ :=
  ∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), P (i.insertNth s y) i k

noncomputable def boxSurfaceForce (P : Vec3 → Stress) (a b : Vec3) (k : Fin 3) : ℝ :=
  ∑ i, (faceIntegral P a b i (b i) k - faceIntegral P a b i (a i) k)

/-- A force density `f` "is accounted for by a distribution of stress `P`" on boxes: for every
box, the volume integral of `f` equals the surface integral of the stress over its boundary
(Treatise 1881, vol. I, Art. 105, eqs. (15)–(18), pp. 146–147). Maxwell asks this for *any*
closed surface separating the two systems; boxes are the case Mathlib's divergence theorem covers
today. -/
def AccountedForByStress (P : Vec3 → Stress) (f : Vec3 → Vec3) : Prop :=
  ∀ a b : Vec3, a ≤ b → ∀ k, ∫ x in Set.Icc a b, f x k = boxSurfaceForce P a b k

/-- **Target (expected provable).** Treatise 1881, vol. I, Arts. 104–105, pp. 145–147, and
1873, vol. I, Art. 108, p. 131 ("the mechanical effect of these tensions and pressures on any
portion of the medium, however bounded, will be identical with the mechanical effect of the
electrical forces according to the ordinary theory"): for a `C²` potential with
`∇²Ψ = 4πρ` (Maxwell's sign) the force `ρE` is accounted for by the stress (14). It should follow
from the proved pointwise identity `art105_force` and the divergence theorem on boxes. -/
def Art105DirectAction : Prop :=
  ∀ (Ψ : Vec3 → ℝ) (ρ : Vec3 → ℝ), ContDiff ℝ 2 Ψ → (∀ x, maxwellNabla2 Ψ x = fourPi * ρ x) →
    AccountedForByStress (stress1881 Ψ) (fun x => ρ x • (-grad Ψ x))

/-! ## Energy: the integrations by parts of Arts. 631 and 635 -/

/-- **Target (expected provable, with a sharpened hypothesis).** Treatise 1873, vol. II,
Arts. 630–631, pp. 246–247: `W = ½ ∑ eΨ`, with the quantity of electricity in an element
`(df/dx + dg/dy + dh/dz) dx dy dz`, equals `½ ∭ (Pf + Qg + Rh) dx dy dz` over all space.
Maxwell uses decay at infinity (`Ψ ~ r⁻¹`, `D ~ r⁻²`); the statement uses compact support,
which is stronger. Equality of the two totals is all the mathematics gives: it does **not**
locate the energy. Location is the physical claim of Art. 631 and of 1865, § 74
(`Maxwell.Sources.dyn1865_s74`). -/
def Art631EnergyInField : Prop :=
  ∀ (Ψ : Vec3 → ℝ) (D : Vec3 → Vec3), ContDiff ℝ 1 Ψ → ContDiff ℝ 1 D →
    HasCompactSupport Ψ → HasCompactSupport D →
    (1 / 2) * ∫ x, div D x * Ψ x = ∫ x, electrostaticEnergy631 (-grad Ψ x) (D x)

/-- **Target (expected provable, with a sharpened hypothesis).** Treatise 1873, vol. II,
Arts. 634–635, eqs. (16)–(19), pp. 248–249: `T = ½ ∭ (Fu + Gv + Hw)` over the currents equals
`(1/8π) ∭ (aα + bβ + cγ)` over all space, with `𝔅 = curl 𝔄` (Art. 591) and `4πJ = curl H`
(Art. 607). Compact support replaces Maxwell's decay `H ~ r⁻³`. Again: equal totals, not a
proof of where the energy is. -/
def Art635ElectrokineticInField : Prop :=
  ∀ (A H : Vec3 → Vec3), ContDiff ℝ 1 A → ContDiff ℝ 1 H →
    HasCompactSupport A → HasCompactSupport H →
    (1 / 2) * ∫ x, A x ⬝ᵥ ((1 / fourPi) • curl H x) =
      ∫ x, electrokineticEnergy636 (curl A x) (H x)

/-! ## Art. 616: Maxwell's choice `χ = 0` -/

/-- **Statement of a later justification, not Maxwell's claim.** Art. 616 (p. 235) simply
*supposes* `χ = 0`, so `J = div 𝔄 = 0`. That such a choice is always available (solve a Poisson
equation for `χ`) is later analysis. -/
def Art616GaugeChoiceAvailable : Prop :=
  ∀ A : Vec3 → Vec3, ContDiff ℝ ⊤ A → HasCompactSupport A →
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, div (fun y => A y + grad χ y) x = 0

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
