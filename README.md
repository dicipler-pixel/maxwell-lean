<div align="center">

# Maxwell's own electromagnetism, in Lean

![Lean](https://img.shields.io/badge/Lean-v4.36.0--rc2-blue)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)

Jeromie Beasley

GitHub [dicipler-pixel](https://github.com/dicipler-pixel) · X [@d1c1pler](https://x.com/d1c1pler) ·
YouTube [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae) ·
[atlas-memoriae.dicipler.workers.dev](https://atlas-memoriae.dicipler.workers.dev) ·
ORCID [https://orcid.org/0009-0006-4645-5643](https://orcid.org/0009-0006-4645-5643)

</div>

---

A Lean 4 / Mathlib formalization of **James Clerk Maxwell's work as he wrote it** — not a modern
rewrite of "Maxwell's equations". It follows his steps in the *Treatise on Electricity and
Magnetism* (1st ed. 1873; 2nd ed. 1881) and the 1865 *Dynamical Theory*, in his notation and
Gaussian-style units with explicit `4π`, with the four fields `E`, `D`, `B`, `H` kept distinct
and media allowed. Each of his claims is set out in the strongest form that still matches his
words, including steps he later dropped and limits he stated on his own theory.

## Fidelity rules

1. Every formal statement cites the work, edition, article or section, page in the edition
   used, and the local text file it was checked against.
2. Maxwell's order is kept. Example: the magnetic force law is derived *from the stress* with
   the magnetic-matter term `m` present (Art. 643); `m = 0` enters only as the separate
   Ampère–Weber hypothesis of Art. 644 (`AmpereWeber644`), never as a default.
3. His caveats stay visible and are never papered over: Art. 111 ("I have not been able to make
   the next step"), Art. 645 ("We have asserted nothing as yet with respect to the mode in which
   this state of stress is originated and maintained"), the 1861 model's "provisional and
   temporary character", and 1865 § 82 on gravity ("I cannot go any further"). They are recorded
   verbatim in `Maxwell/Sources.lean` and are not formalized as anything proved.
4. Later ideas are not attributed to him: no field momentum density, no energy-flux (Poynting)
   vector, no point-charge Lorentz law, no hidden momentum, no field theory of gravity. His
   "electromagnetic momentum" is the vector potential and its circuit line-integral.
5. Proved results contain no `sorry` and use only the three standard axioms. Unproved claims
   are `Prop`s in `Maxwell/Statements.lean`, which the root module does not import.

## What is proved

All with no `sorry`; `scripts/Axioms.lean` audits 64 theorems (`propext`, `Classical.choice`,
`Quot.sound` only).

| Maxwell | Lean name | File |
|---|---|---|
| 1873 Art. 108 eqs. (1)–(5): three tensions with `p' = p'' = −p` give tension `p` along `R` with equal lateral pressure | `art108_superposition` | `Treatise/ElectrostaticStress.lean` |
| 1873 Art. 108 eq. (6), `R² = 8πp`: components `p_xx = (X² − Y² − Z²)/8π`, `p_xy = XY/4π` | `art108_components`, `componentForm_xx_xy` | same |
| 1873 Art. 108 eqs. (7)–(10): the stress gives the force `ρR` on an element (using Art. 77, no curl) | `art108_force` | same |
| 1881 Arts. 103–105 eqs. (6), (14)–(15): from `∇²Ψ = 4πρ` (his sign), the stress (14) gives `−ρ ∇Ψ` | `art105_force` | same |
| 1881 Art. 105 eqs. (15)–(18), on boxes: volume integral of `ρE` equals the surface integral of the stress (14) | `art105_directAction` | same |
| 1881 Art. 106: tension along `E`, equal pressure across it, two principal stresses equal and the third reversed (mutually perpendicular unit frame, `E ≠ 0`) | `art106_tension`, `art106_pressure`, `art106_principal` | same |
| 1873 Art. 111, p. 134: a polarized dielectric "is the seat of electrical energy"; energy per unit volume equals the tension, `p = ½ 𝔇 𝔈 = (1/8π) K 𝔈² = (2π/K) 𝔇²`; Art. 107's `p = R²/8π` is the `K = 1` case | `art111_energy_eq_tension`, `art107_tension_of_art111` | same |
| Art. 641 eq. (15): the magnetic stress `P_hk = B_h H_k/4π − δ_hk H²/8π`; its couple is `B × H/4π` | `art641_components`, `art641_couple` | `Treatise/MagneticStress.lean` |
| Art. 641: symmetric **iff** `B × H = 0` ("this condition … is not fulfilled" in magnets) | `art641_symm_iff` | same |
| Art. 639 eq. (2) with Art. 400: stress couple = `I × H` | `art639_couple` | same |
| Arts. 639–641: stress force = `A dα/dx + B dβ/dx + C dγ/dx + vc − wb` (Art. 403 used in Art. 640 eq. (8), p. 253) | `art641_force` | same |
| Art. 642 eq. (17): bisector decomposition — pressure `H²/8π`, tension, pressure, couple `𝔅ℌ sin 2ε/4π` from `B` toward `H`; eq. (18) when `B` is in the same direction as `H` (his case `μ > 0`): hydrostatic pressure `H²/8π` plus longitudinal tension `μ H²/4π` | `art642_bisector`, `art642_parallel`, `art642_along_H` | same |
| Art. 643: unmagnetized stress = tension `H²/8π` along lines + equal lateral pressure | `art643_unmagnetized`, `art643_tension_pressure` | same |
| Art. 643, eq. (20), p. 257, Equations of Electromagnetic Force: `X = αm + vγ − wβ` from the stress, `m` the austral magnetic matter | `art643_force`, `art643_force_components` | same |
| Our observation, not his route: `B = H` with Art. 403 forces `m = 0` | `art643_m_eq_zero_of_art403` | same |
| Art. 645, as his hypothesis: the superposed stress produces `ρE + mH + J × H` | `stress645`, `art645_force` | same |
| Art. 644, p. 257: **under the Ampère–Weber hypothesis** `m = 0` and eq. (21) `div H = 0`; eq. (22) `X = vγ − wβ` | `AmpereWeber644`, `art644_force` | same |
| Arts. 630–636: `½ E·D` (potential) and `B·H/8π` (kinetic), in his classification | `electrostaticEnergy631`, `electrokineticEnergy636`, `energy_isotropic` | `Treatise/Energy.lean` |
| Art. 792: pressure normal to the wave equals the whole energy per unit volume, **from the stresses** | `art792_radiation_pressure`, `art792_radiation_pressure_components` | `Treatise/RadiationPressure.lean` |
| Art. 792 against Arts. 641–642 for `B = μH` (sharpening) | `art642_normalStress_transverse`, `art642_vs_art792` | same |
| Arts. 598–599: `𝔈 = 𝔊 × 𝔅 − 𝔄̇ − ∇Ψ`; motional part normal to the parallelogram, area, right-handed | `emf598`, `art598_components`, `art599_motional` | `Treatise/ElectromotiveForce.lean` |
| Arts. 590, 604: electromagnetic momentum of a circuit = line-integral of `𝔄` | `circuitMomentum` | `Treatise/VectorPotential.lean` |
| Arts. 598, 616: `χ` "disappears from the equations (A)" and from the circuit integral | `art616_induction_unchanged`, `art616_circuitMomentum_unchanged` | same |

## What is stated but not proved

`Maxwell/Statements.lean` (statements only, as `Prop`s):

* `Art631EnergyInField`, `Art635ElectrokineticInField` — his integrations by parts, with
  compact support as a stepping stone. Equal totals do not locate the energy; Art. 631 itself
  is an equal-totals claim ("will be the same if we suppose that it resides…"). Location is
  the physical claim of 1865 § 74, the hypothesis of Art. 636, and 1873 Art. 111 ("is the seat
  of electrical energy").
* `Art631EnergyInFieldDecay`, `Art635ElectrokineticInFieldDecay` — the same equalities under
  his decay rates (`Ψ ~ r⁻¹`, `D ~ r⁻²`, `H ~ r⁻³`) and, for Art. 635, our added `A ~ r⁻²`
  (he prints only `H ~ r⁻³`). A `C¹` `D` still excludes Art. 630 surface charges.
* `Art590Impulse` — why 𝔄 is called a momentum: the impulse of the EMF when the current is
  stopped (Art. 590). Lagrangian / generalized (Art. 604), not a field momentum density.
* `Art634KineticEnergy` — the shape of Art. 634's claim `T = ½ ∑ pᵢ iᵢ = ½ ∭ 𝔄·J`. The link
  between the circuits and `J` is not yet formalized, so this is not yet a closed target.
* `Art616GaugeChoiceAvailable` — Maxwell's construction (Art. 616 eqs. (5)–(7),
  `χ = (1/4π)∭ J/r`, his `J = div 𝔄`, not the current); general existence and regularity
  are later rigor.
* `Art617Uniqueness` — Art. 617: when the distribution of electric currents is given, one,
  and only one, 𝔄 that is finite and continuous, satisfies `∇²𝔄 = 4πμ𝔊` and `div 𝔄 = 0`,
  and vanishes at infinity, with `μ` uniform and `div 𝔊 = 0` (Art. 607 (E)).
* `TotalMagnetismZero377` — his empirical position (totals), distinct from Art. 644's `m = 0`.
* `GravityMediumEnergyNonneg1865` — what the gravity analogy would require (1865 § 82), recorded
  as the dead end he called it.

## Where Maxwell's wording had to be sharpened

* **Maxwell's `∇²` is minus the Laplacian** (footnote to Art. 616, and 1881 vol. I, Art. 103,
  eq. (3)). `maxwellNabla2` keeps his sign, so `∇²Ψ = 4πρ` is Poisson's equation.
* **Art. 108 and Art. 111 in a dielectric.** Arts. 107–108 carry no `K` (they use Art. 77,
  i.e. the `K = 1` case); Art. 111
  (p. 134) asserts that a polarized dielectric "is the seat of electrical energy" and prints
  `p = ½ 𝔇 𝔈 = (1/8π) K 𝔈² = (2π/K) 𝔇²` (checked against the page image). Art. 107's
  `p = R²/8π` is the `K = 1` corollary, not a disagreement.
* **Art. 640 uses `div B = 0` (Art. 403, eq. (8), p. 253) to reduce (7) to (9), which Art. 641's
  stress matches; Art. 643 sets `B = H` and keeps `div H = 4πm`.** Together these would force
  `m = 0`. That inference is ours (`art643_m_eq_zero_of_art403`), not Maxwell's: he reaches
  `m = 0` by the Ampère–Weber hypothesis of Art. 644. The two routes are kept apart: Art. 403
  is an explicit hypothesis of `art641_force` only.
* **Art. 792 does not need the equal halves (eq. (8))**: the normal pressure is the sum of the two
  energies for any transverse disturbance. And Art. 792 cites Art. 643 (`B = H`); with the
  magnetized stress of Art. 642 and `B = μH` the magnetic pressure is `H²/8π`, which equals the
  energy `μH²/8π` only when `μ = 1` (`art642_vs_art792`).
* **Most force theorems are pointwise** at a point with differentiability (or `C²`) hypotheses;
  Maxwell's statements about "any portion of the medium" are the integrated forms. The box case
  of 1881 Art. 105 is now proved (`art105_directAction`); "any closed surface" is not.
## Build

```
lake exe cache get   # Mathlib pin 1b1ccf4b088b32fa3f23f2de1127433254a81e1e
lake build
./scripts/check_axioms.sh
```

## Sources

Public-domain scans (archive.org OCR): *Treatise*, 1st ed. 1873, vols. I–II
(`electricandmagne01maxwrich`, `electricandmagne02maxwrich`); 2nd ed. 1881, vol. I
(`treatiseonelectr01maxwrich`); Niven (ed.), *Scientific Papers* I–II, CUP 1890
(`scientificpapers01maxwuoft`, `scientificpapers02maxwuoft`). See `DESIGN.md`.

## Credits

Formalization by Jeromie Beasley, drafted with AI assistance (Lean Green PR Machine, a Grok Bot
agent, following fidelity constraints from Grey and an architecture plan from ink). Grey reviewed
the wording twice; ink drafted the patches. This commit applies both reviews (Art. 617 now
requires a solenoidal current; the material-current quote is Art. 574). Jeromie Beasley's own
papers were used only as a lens for reading Maxwell, never as a source for any statement here;
see `NOTES-resemblances.md`.

Code: MIT (see `LICENSE`).
