# Design: Maxwell's path, and what gets formalized in his order

This library formalizes Maxwell's statements, not their modern descendants. Physlib's free-space
equations (`leanprover-community/physlib`) and other Lean electromagnetism projects are not
dependencies and not templates. Only Mathlib infrastructure is used (`Fin 3 → ℝ`, `Matrix` for
possibly non-symmetric stress, `fderiv`, the cross product, interval integrals; later the
divergence theorem on boxes). The Hodge-star module is avoided while it still has TODOs.

## Historical path

1. *On Faraday's Lines of Force* (1855–56) — geometrical analogy. (`FaradayLines.lean`, later.)
2. *On Physical Lines of Force* (1861–62) — vortices and idle wheels, explicitly "provisional and
   temporary" (Sci. Papers I, p. 486); stress as tension along the lines (p. 455); for gravity
   "the stress along the lines of gravitating force must be a pressure" (p. 455).
   (`PhysicalLines.lean`, later.)
3. *A Dynamical Theory of the Electromagnetic Field* (1865) — mechanical words are "illustrative,
   not explanatory", but energy is meant "literally" (§ 74); electromagnetic momentum `F, G, H`
   and its circuit integral (§§ 57–58); the gravity note ends "I cannot go any further" (§ 82).
   (`DynamicalTheory.lean`, later.)
4. *Treatise*, 1873; 2nd ed. 1881 (first nine chapters revised by Maxwell).

## What is formalized, in his order (status in this pass)

| Step | Source | Status |
|---|---|---|
| Electrostatic tension `p` along `R` with equal lateral pressure, `R² = 8πp`; superposition; components; force `ρR` | 1873 I, Arts. 107–108 | proved |
| Faraday's statement of the same distribution | 1873 I, Art. 109 | cited only |
| Energy per unit volume = tension = `p = ½ 𝔇 𝔈 = (1/8π) K 𝔈² = (2π/K) 𝔇²`; a polarized dielectric "is the seat of electrical energy" | 1873 I, Art. 111, p. 134 | printed formula proved (page image); Art. 107 is the `K = 1` corollary; location and limit recorded |
| Potential `Ψ`, components (14), direct-action surface-integral test | 1881 I, Arts. 103–105 | pointwise proved; integrated form proved on boxes (`art105_directAction`); "any closed surface" not formalized |
| Type of the stress: two principal stresses equal, third reversed | 1881 I, Art. 106 | proved |
| Force and couple on magnetized element with current | 1873 II, Arts. 639–640 | proved (as the target of Art. 641) |
| Non-symmetric magnetic stress, couple `B × H/4π` | 1873 II, Art. 641 | proved |
| Bisector decomposition, couple from `B` toward `H`, isotropic part `H²/8π` | 1873 II, Art. 642 | proved |
| Unmagnetized stress; force `X = αm + vγ − wβ` with magnetic matter | 1873 II, Art. 643 | proved |
| Ampère–Weber: `m = 0` as a hypothesis; force `J × H` | 1873 II, Art. 644 | proved under hypothesis |
| No account of how the stress is maintained; superposition of stresses | 1873 II, Art. 645 | limit recorded (including "unfruitful"); superposition defined (`stress645`) and its force proved as his hypothesis |
| Energy split: electric potential `½E·D`, magnetic kinetic `B·H/8π`; Art. 631 is equal totals ("if we suppose"), not a location claim | 1873 II, Arts. 630–636 | densities defined; integrals stated (compact-support and decay-rate targets) |
| Energy "literally" in the field | 1865 § 74 (with § 73 "illustrative, not explanatory"); also Art. 636 (hypothesis) and 1873 Art. 111 ("seat of electrical energy") | recorded claims (physical) |
| Electromagnetic momentum = vector potential; circuit line-integral | 1873 II, Arts. 590, 604; 1865 §§ 57–58 | defined |
| `v × B` in the electromotive intensity at a moving point | 1873 II, Arts. 598–599 | proved (geometry) |
| `χ` disappears; constructed as `(1/4π)∭ J/r` (his `J = div 𝔄`, not the current) then set to zero | 1873 II, Arts. 616–617 | proved (invariance, more general than his specific `χ`); uniqueness stated under uniform `μ` and `div 𝔊 = 0` (Art. 607 (E)) |
| Momentum is not that of the electricity; null experiments | 1873 II, Arts. 549, 574–575 | recorded |
| Radiation pressure = energy per unit volume, from the stresses | 1873 II, Art. 792 | proved, with two sharpenings |
| A medium for energy in transit (no flux vector) | 1873 II, Art. 866 | recorded |
| Gravity as stress: enormous intrinsic energy, dead end | 1865 § 82 | stated limit |

## Not formalized as his

Field momentum density (`D × H/4πc`: J. J. Thomson 1891, Heaviside, Poincaré 1900, Abraham
1903), the Poynting vector (1884), the point-charge Lorentz force, Minkowski's or Abraham's
tensors, hidden momentum, and full gauge invariance of `(𝔄, Ψ)`. If any is added for
comparison it goes in a separate, labelled "later" module.

## Conventions

* Axes `x, y, z` = indices `0, 1, 2`; fields are `Vec3 → Vec3`.
* `P h k`: normal along `h`, force along `k`, exerted by the positive side (Art. 641).
  `stressForce P = ∑_h ∂_h P_hk` (Art. 641 eq. (13); Art. 108).
* Treatise units with explicit `4π`; nothing converted to SI.

## Next steps (for review by Grey and ink)

1. ~~Prove `Art105DirectAction` on boxes from `art105_force` and Mathlib's divergence theorem.~~
   Done (`art105_directAction`); Maxwell's "any closed surface" remains open.
2. ~~Prove `Art631EnergyInField` / `Art631EnergyInFieldDecay` and
   `Art635ElectrokineticInField` / `Art635ElectrokineticInFieldDecay` (integration by parts).~~
   Done, both compact-support and decay versions (`art631_energyInField`,
   `art631_energyInFieldDecay`, `art635_electrokineticInField`,
   `art635_electrokineticInFieldDecay`, via `integral_div_eq_zero_of_decay` on cubes). Still
   open nearby: `Art616GaugeChoiceAvailable` and the existence half of `Art617Uniqueness`
   (Newtonian potential), the uniqueness half (Liouville on `ℝ³`), and `Art634KineticEnergy`
   (shape only).
3. Read Faraday's Lines, Physical Lines, and the 1865 paper in full before writing
   `FaradayLines.lean`, `PhysicalLines.lean`, `DynamicalTheory.lean`.
4. Treatise vol. II ch. IX general equations (Arts. 604–619) with `K`, `μ`, conductivity.
5. ~~Confirm Art. 111's printed formula against a page image before restating `art111` as
   `p = ½ D·E = K E²/8π`, with Art. 107 as the `K = 1` corollary.~~
   Done (`art111_energy_eq_tension` is `p = ½ 𝔇 𝔈 = (1/8π) K 𝔈² = (2π/K) 𝔇²`, checked against
   Internet Archive `electricandmagne01maxwrich`, page n171; `art107_tension_of_art111` is the `K = 1` corollary).
6. ~~Confirm Art. 643's force-law equation number against a page image.~~
   Done: 1873 vol. II p. 257 (Internet Archive `electricandmagne02maxwrich`) labels the
   force law "(Equations of Electromagnetic Force.) (20)". Art. 644's
   `dα/dx + dβ/dy + dγ/dz = 0` is (21); the reduced force is (22).
