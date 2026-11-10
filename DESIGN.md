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
| Energy per unit volume = tension = `½ D·R`; Art. 111 limit | 1873 I, Art. 111 | proved (algebra); limit recorded |
| Potential `Ψ`, components (14), direct-action surface-integral test | 1881 I, Arts. 103–105 | pointwise proved; integrated form stated |
| Type of the stress: two principal stresses equal, third reversed | 1881 I, Art. 106 | proved |
| Force and couple on magnetized element with current | 1873 II, Arts. 639–640 | proved (as the target of Art. 641) |
| Non-symmetric magnetic stress, couple `B × H/4π` | 1873 II, Art. 641 | proved |
| Bisector decomposition, couple from `B` toward `H`, isotropic part `H²/8π` | 1873 II, Art. 642 | proved |
| Unmagnetized stress; force `X = αm + vγ − wβ` with magnetic matter | 1873 II, Art. 643 | proved |
| Ampère–Weber: `m = 0` as a hypothesis; force `J × H` | 1873 II, Art. 644 | proved under hypothesis |
| No account of how the stress is maintained; superposition of stresses | 1873 II, Art. 645 | limit recorded; superposition used |
| Energy split: electric potential `½E·D`, magnetic kinetic `B·H/8π` | 1873 II, Arts. 630–636 | densities defined; integrals stated |
| Energy "literally" in the field | 1865 § 74 | recorded claim (physical) |
| Electromagnetic momentum = vector potential; circuit line-integral | 1873 II, Arts. 590, 604; 1865 §§ 57–58 | defined |
| `v × B` in the electromotive intensity at a moving point | 1873 II, Arts. 598–599 | proved (geometry) |
| `χ` disappears; set to zero | 1873 II, Art. 616 | proved (invariance); choice stated as later |
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

1. Prove `Art105DirectAction` on boxes from `art105_force` and Mathlib's divergence theorem.
2. Prove `Art631EnergyInField` and `Art635ElectrokineticInField` (integration by parts).
3. Read Faraday's Lines, Physical Lines, and the 1865 paper in full before writing
   `FaradayLines.lean`, `PhysicalLines.lean`, `DynamicalTheory.lean`.
4. Treatise vol. II ch. IX general equations (Arts. 604–619) with `K`, `μ`, conductivity.
