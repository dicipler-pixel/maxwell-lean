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

All with no `sorry`; `scripts/Axioms.lean` audits 54 theorems (`propext`, `Classical.choice`,
`Quot.sound` only).

| Maxwell | Lean name | File |
|---|---|---|
| 1873 Art. 108 eqs. (1)–(5): three tensions with `p' = p'' = −p` give tension `p` along `R` with equal lateral pressure | `art108_superposition` | `Treatise/ElectrostaticStress.lean` |
| 1873 Art. 108 eq. (6), `R² = 8πp`: components `p_xx = (X² − Y² − Z²)/8π`, `p_xy = XY/4π` | `art108_components`, `componentForm_xx_xy` | same |
| 1873 Art. 108 eqs. (7)–(10): the stress gives the force `ρR` on an element (using Art. 77, no curl) | `art108_force` | same |
| 1881 Arts. 103–105 eqs. (6), (14)–(15): from `∇²Ψ = 4πρ` (his sign), the stress (14) gives `−ρ ∇Ψ` | `art105_force` | same |
| 1881 Art. 106: tension along `E`, equal pressure across it, two principal stresses equal and the third reversed | `art106_tension`, `art106_pressure`, `art106_principal` | same |
| 1873 Art. 111: energy per unit volume `½ E·D` equals the tension (exactly when `K = 1` for Art. 107's `p`) | `art111_energy_eq_tension` | same |
| Art. 641 eq. (15): the magnetic stress `P_hk = B_h H_k/4π − δ_hk H²/8π`; its couple is `B × H/4π` | `art641_components`, `art641_couple` | `Treatise/MagneticStress.lean` |
| Art. 641: symmetric **iff** `B × H = 0` ("this condition … is not fulfilled" in magnets) | `art641_symm_iff` | same |
| Art. 639 eq. (2) with Art. 400: stress couple = `I × H` | `art639_couple` | same |
| Arts. 639–641: stress force = `A dα/dx + B dβ/dx + C dγ/dx + vc − wb` (with his Art. 403 step) | `art641_force` | same |
| Art. 642 eq. (17): bisector decomposition — pressure `H²/8π`, tension, pressure, couple `𝔅ℌ sin 2ε/4π` from `B` toward `H`; tangential stresses vanish when `B ∥ H` | `art642_bisector`, `art642_parallel` | same |
| Art. 643: unmagnetized stress = tension `H²/8π` along lines + equal lateral pressure | `art643_unmagnetized`, `art643_tension_pressure` | same |
| Art. 643 eq. (21): `X = αm + vγ − wβ` from the stress, `m` the austral magnetic matter | `art643_force`, `art643_force_components` | same |
| Art. 644 eq. (22): **under the Ampère–Weber hypothesis** `m = 0`, `X = vγ − wβ` | `AmpereWeber644`, `art644_force` | same |
| Arts. 630–636: `½ E·D` (potential) and `B·H/8π` (kinetic), in his classification | `electrostaticEnergy631`, `electrokineticEnergy636`, `energy_isotropic` | `Treatise/Energy.lean` |
| Art. 792: pressure normal to the wave equals the whole energy per unit volume, **from the stresses** | `art792_radiation_pressure`, `art792_radiation_pressure_components` | `Treatise/RadiationPressure.lean` |
| Art. 792 against Arts. 641–642 for `B = μH` (sharpening) | `art642_normalStress_transverse`, `art642_vs_art792` | same |
| Arts. 598–599: `𝔈 = 𝔊 × 𝔅 − 𝔄̇ − ∇Ψ`; motional part normal to the parallelogram, area, right-handed | `emf598`, `art598_components`, `art599_motional` | `Treatise/ElectromotiveForce.lean` |
| Arts. 590, 604: electromagnetic momentum of a circuit = line-integral of `𝔄` | `circuitMomentum` | `Treatise/VectorPotential.lean` |
| Arts. 598, 616: `χ` "disappears from the equations (A)" and from the circuit integral | `art616_induction_unchanged`, `art616_circuitMomentum_unchanged` | same |

## What is stated but not proved

`Maxwell/Statements.lean` (statements only, as `Prop`s):

* `Art105DirectAction` — the integrated direct-action test on boxes (1881 Art. 105; 1873
  Art. 108 "however bounded"). Expected to follow from `art105_force` plus Mathlib's divergence
  theorem.
* `Art631EnergyInField`, `Art635ElectrokineticInField` — his integrations by parts, with
  compact support in place of his decay at infinity. Equal totals do not locate the energy;
  the location is the physical claim of 1865 § 74.
* `Art616GaugeChoiceAvailable` — that `χ` can always be chosen to make `div 𝔄 = 0`. Later
  analysis; Art. 616 simply supposes it.
* `TotalMagnetismZero377` — his empirical position (totals), distinct from Art. 644's `m = 0`.
* `GravityMediumEnergyNonneg1865` — what the gravity analogy would require (1865 § 82), recorded
  as the dead end he called it.

## Where Maxwell's wording had to be sharpened

* **Maxwell's `∇²` is minus the Laplacian** (footnote to Art. 616). `maxwellNabla2` keeps his
  sign, so `∇²Ψ = 4πρ` is Poisson's equation.
* **Art. 108 and Art. 111 in a dielectric.** Art. 107's `R² = 8πp` has no `K`; Art. 111 equates
  the tension to `½ D·R`. These agree exactly when `K = 1`.
* **Art. 641 uses `div B = 0` (Art. 403); Art. 643 sets `B = H` and keeps `div H = 4πm`.**
  Together these would force `m = 0`, which is what Art. 644 then adopts. The two routes are kept
  apart: Art. 403 is an explicit hypothesis of `art641_force` only.
* **Art. 792 does not need the equal halves (eq. (8))**: the normal pressure is the sum of the two
  energies for any transverse disturbance. And Art. 792 cites Art. 643 (`B = H`); with the
  magnetized stress of Art. 642 and `B = μH` the magnetic pressure is `H²/8π`, which equals the
  energy `μH²/8π` only when `μ = 1` (`art642_vs_art792`).
* **Theorems are pointwise** at a point with differentiability (or `C²`) hypotheses; Maxwell's
  statements about "any portion of the medium" are the integrated forms in `Statements`.

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
agent, following fidelity constraints from Grey and an architecture plan from ink; their review of
this pass is pending). Jeromie Beasley's own papers were used
only as a lens for reading Maxwell, never as a source for any statement here; see
`NOTES-resemblances.md`.

Code: MIT (see `LICENSE`).
