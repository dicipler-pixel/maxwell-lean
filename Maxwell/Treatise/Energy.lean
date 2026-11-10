/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.MagneticStress

/-!
# Energy per unit volume, with Maxwell's split (Treatise 1873, vol. II, Arts. 630–638)

Art. 630 (p. 246): "THE energy of the system may be divided into the Potential Energy and the
Kinetic Energy." Maxwell's assignment is kept, and is the **reverse** of the later Lagrangian
bookkeeping in which `½E²` is the kinetic-like term and `B²` the potential-like term:

* electric energy is **potential**, "half the product of the electromotive force and the
  electric displacement, multiplied by the cosine of the angle which these vectors include" —
  `½ E·D` (Art. 631, p. 247). Art. 631's claim is about **totals** and is conditional: "the
  electrostatic energy of the whole field will be the same *if we suppose* that it resides in every
  part of the field where electrical force and electrical displacement occur, instead of being
  confined to the places where free electricity is found" (`Maxwell.Sources.art631`);
* magnetic (electrokinetic) energy is **kinetic**, `(1/8π) B·H` per unit volume, and "this
  energy exists in the form of some kind of motion of the matter in every portion of space"
  (Art. 636, p. 249). The "some kind of motion" clause is Maxwell's hypothesis (he points ahead
  to Art. 821); it is recorded in `Maxwell.Sources.art636`, not proved.

Where Maxwell *locates* the energy, he does so elsewhere: literally in 1865, § 74 ("On our theory
it resides in the electromagnetic field", `Maxwell.Sources.dyn1865_s74`; with § 73's "illustrative,
not as explanatory" for the mechanical words, `dyn1865_s73`), as a hypothesis in Art. 636 ("According
to our hypothesis, we assume the kinetic energy to exist wherever there is magnetic force"), and in
1873 vol. I, Art. 111 ("A dielectric medium, when thus polarized, is the seat of electrical energy",
`Maxwell.Sources.art111_energy`).

Only the *densities* are defined here. That the two volume integrals equal the old expressions
`½∑eΨ` (Art. 631) and `½∑pi` (Arts. 634–635) is stated in `Maxwell.Statements`; equal totals do
not locate the energy, and the location claims above are physical claims no integral identity can
prove.

Local source: `/workspace/maxwell_reread/n_electricandmagne02maxwrich.txt`.
-/

namespace Maxwell

open Matrix

/-- The two forms of energy in Art. 630. -/
inductive EnergyForm
  | potential
  | kinetic
  deriving DecidableEq, Repr

/-- **Art. 631, p. 247:** electrostatic energy per unit volume, `½ E·D` (in quaternion language
`−½ S𝔈𝔇`). -/
noncomputable def electrostaticEnergy631 (E D : Vec3) : ℝ := (1 / 2) * (E ⬝ᵥ D)

/-- Maxwell's classification of `electrostaticEnergy631` (Arts. 630–631): potential energy. -/
def electrostaticEnergy631.form : EnergyForm := .potential

/-- **Art. 635, eq. (19), and Art. 636, p. 249:** electrokinetic energy per unit volume,
`(1/8π) B·H` (in quaternion language `−(1/8π) S𝔅ℌ`). -/
noncomputable def electrokineticEnergy636 (B H : Vec3) : ℝ := (1 / (8 * Real.pi)) * (B ⬝ᵥ H)

/-- Maxwell's classification of `electrokineticEnergy636` (Arts. 634–636, and the end of
Art. 638: "both magnetic and electromagnetic energy as kinetic energy"): kinetic energy. -/
def electrokineticEnergy636.form : EnergyForm := .kinetic

/-- **Art. 792, eqs. (22)–(23), p. 391** (isotropic medium, `4π D = K E`, `B = μ H`): the two
densities are `K E²/8π` and `μ H²/8π`. -/
theorem energy_isotropic (K μ : ℝ) (E H : Vec3) :
    electrostaticEnergy631 E ((K / fourPi) • E) = K * sq E / (8 * Real.pi) ∧
    electrokineticEnergy636 (μ • H) H = μ * sq H / (8 * Real.pi) := by
  constructor
  · simp [electrostaticEnergy631, sq, dotProduct_smul, fourPi]; field_simp; ring
  · simp [electrokineticEnergy636, sq, smul_dotProduct]; field_simp

end Maxwell
