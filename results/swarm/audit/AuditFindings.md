# Adversarial audit of the load-bearing stress/energy theorems (direction d2)

Files (all in `.ultramath/smwatx3t5/m6/`):

| file | content |
|---|---|
| `Audit.lean` | the audit: 51 theorems, no `sorry`; imports `Maxwell.Treatise.RadiationPressure` |
| `Axioms.lean`, `axioms-output.txt` | `#print axioms` for all 51: only `propext`, `Classical.choice`, `Quot.sound` |
| `shim/Maxwell/...` | verbatim copy of the repo's 8 modules + one added `import` (see §0) |
| `AuditFindings.md` | this file |

Exact commands (run in the repo root `/workspace/nucleus/work/projects/p-c1e28406062a4279aca922483c0a99ab/repo`):

```bash
M=$PWD/.ultramath/smwatx3t5/m6
export LEAN_PATH="$M/oleans:$LEAN_PATH"
# 1. build the repo's modules at 4.33.1 (from the shim copy, which is byte-identical
#    except for one added import)
cd $M/shim && for f in Maxwell/Basic Maxwell/Treatise/ElectrostaticStress \
    Maxwell/Treatise/MagneticStress Maxwell/Treatise/Energy Maxwell/Treatise/RadiationPressure; do
  lean -o $M/oleans/$f.olean $f.lean; done
# 2. the audit itself
cd $M && lean Audit.lean          # 0 errors, 0 sorry
# 3. axioms
cd $M && lean -o oleans/Audit.olean Audit.lean && lean Axioms.lean
```

## 0. The repo does not compile against the available Mathlib 4.33.1

`Maxwell/Treatise/ElectrostaticStress.lean:338` uses `dotProduct_self_eq_zero.mp`; in 4.33.1 that
lemma is in `Mathlib.LinearAlgebra.Matrix.DotProduct`, which the file does not import (the error is
`unknown identifier dotProduct_self_eq_zero.mp`). Adding

```lean
import Mathlib.LinearAlgebra.Matrix.DotProduct
```

is the **only** change needed: with it, `Basic`, `ElectrostaticStress`, `MagneticStress`, `Energy`,
`RadiationPressure` all compile unchanged at 4.33.1 (`shim/` holds exactly that copy). No statement,
hypothesis or proof step is altered, so the audit below is of the repository's real statements.

## 1. Method

For each audited theorem I did three things in Lean:

* **non-vacuity**: a `*_model` / `*_nonvacuous` theorem that satisfies every hypothesis and
  evaluates the conclusion to a *nonzero* number, independently of the theorem under audit where
  possible (the computation `stressForce (componentForm ∘ id) = (3/4π) • x` is done twice: once by
  hand in `stressForce_componentForm_id`, once through `art108_force` in `art108_force_at_id`);
* **load-bearing hypotheses**: a `*_needs_*` counterexample where dropping one hypothesis makes the
  conclusion false;
* **numeric evaluation** of the printed formula at explicit rational vectors, compared with the
  Lean definition (values carried by hand as rational multiples of `1/π`).

## 2. Verdicts

### arts. 107–108–111 (electrostatic stress, energy)

* `art108_force` — **sound**. Both hypotheses are genuine: `stressForce_componentForm` shows the
  force is `(div R/4π)R + (1/4π)(curl R)×R`, so `curl R = 0` is needed for `ρ R`, and
  `div R = 4πρ` is Art. 77. Non-vacuous: `R = id` gives `ρ = 3/4π` and force `(3/4π)x ≠ 0`
  (`art108_force_at_id`, `art108_force_nonvacuous`). Docstring's "pointwise here, integrated in
  `Statements`" is honest.
* `art105_force` — **sound**. `Ψ = −½|x|²` has `∇²Ψ = 3` in Maxwell's sign, so `ρ = 3/4π`, and the
  force is `(3/4π)x ≠ 0` (`art105_force_at_quadratic`). The Poisson hypothesis is satisfiable with
  `ρ ≠ 0`.
* `art111_energy_eq_tension` — **the numbers are right, two gaps**:
  1. `hK : K ≠ 0` is **redundant**: Lean's total division makes the `K = 0` case true as well, so
     the identity holds for every real `K` (`art111_energy_eq_tension_all`). Harmless, but the
     hypothesis is not doing the work the docstring implies.
  2. The theorem attaches `p` to **no stress matrix**. The only Art. 111 stress in the library is
     `componentForm E`, which has `K = 1`; for `K ≠ 1` its tension is `E²/8π`, *not* `K E²/8π`
     (`art111_componentForm_not_dielectric`). So "energy per unit volume = tension on unit area" was
     proved only as a numerical identity plus the `K = 1` corollary `art107_tension_of_art111`.
     **Repair** (proposed, in `Audit.lean`): `dielectricStress K E`, `p_hk = K E_hE_k/4π −
     δ_hk K E²/8π`, with
     * `dielectricStress_art107`: tension along `E = r u` equals `½𝔇𝔈 = K r²/8π`, and the pressure
       across `E` is the same number — Art. 107/111 for **every** `K`;
     * `stressForce_dielectricStress` / `art111_force_dielectric`: the force per unit volume is
       `(div 𝔇) • 𝔈`, `𝔇 = (K/4π)𝔈`;
     * `dielectricStress_K_one_force`: with `K = 1` this is exactly Art. 108's `ρ • E`
       (`div E = 4πρ`);
     * `dielectricStress_one`: `K = 1` is literally the existing `componentForm`.
     Numeric check: `K = 3`, `𝔈 = (1,2,2)`, `𝔇 = (3/4π)𝔈`: `p = 27/8π` by both printed forms, and
     the traction along `û = 𝔈/3` is `p û` (`art111_numeric`).

### arts. 639–643 (magnetic stress)

* `art641_force` — **sound, and Art. 403 is load-bearing**. With `B = H = x`, `I = J = 0` every
  hypothesis except `div B = 0` holds (`div B = 3`) and the conclusion fails: the stress force is
  `(3/4π)x ≠ 0` while `∑ᵢIᵢ∂ₖHᵢ + (J×B)ₖ = 0` (`art641_force_needs_art403`). So the theorem is
  exactly as strong as Maxwell's use of `da/dx+db/dy+dc/dz = 0` and cannot be extended to general
  `B`. The magnetized case is **not vacuous**: `B = 0`, `H = x`, `I = −H/4π`, `J = 0` satisfies
  `B = H + 4πI`, `curl H = 4πJ`, `div B = 0` with `I ≠ 0`, and gives force `−x/4π`
  (`art641_force_magnetized_model`). The printed eq. (4) `X = A dα/dx + B dβ/dx + C dγ/dx + vc − wb`
  is componentwise the Lean RHS `∑ᵢ Iᵢ ∂ₖHᵢ + (J×B)ₖ` (spelled out for 643 in the repo's
  `art643_force_components`; the analogous componentwise restatement of eq. (4) for 641 is missing
  from the library but is immediate).
* `art642_bisector` — **eq. (17) verified**, symbolically by the theorem and with exact rationals
  `sin ε = 3/5`, `cos ε = 4/5`, `𝔅 = 2`, `ℌ = 3`: `P_xx = −33/200π = −ℌ²/8π + 𝔅ℌcos²ε/4π`,
  `P_yy = −333/200π = −ℌ²/8π − 𝔅ℌsin²ε/4π`, `P_zz = −9/8π`, `P_xy = 18/25π = −P_yx`, and the couple
  is `36/25π = 𝔅ℌ sin2ε/4π` (`art642_bisector_numeric`, `art642_bisector_arithmetic`). The *sense*
  claimed in prose ("tending to turn every element … from the direction of magnetic induction to
  the direction of magnetic force") is correct: for `𝔅, ℌ > 0`, `0 < ε < π/2` the couple about `z`
  is strictly positive, which rotates the element from angle `−ε` (`B`) toward `+ε` (`H`)
  (`art642_couple_pos`).
* `art642_along_H` — **eq. (18) verified** for `B = 3H`, `H = (0,0,2)`: `P_zz = 5/2π =
  (𝔅ℌ − ½ℌ²)/4π` and `P_xx = P_yy = −1/2π = −ℌ²/8π`, i.e. hydrostatic pressure `ℌ²/8π` plus
  longitudinal tension `𝔅ℌ/4π` (`art642_along_H_numeric`).
* `art643_force` — **sound and non-vacuous** with `m = 3/4π ≠ 0` (`art643_force_at_id`,
  `art643_force_nonvacuous`); it assumes no `div H = 0`, as the docstring says.

### Art. 792 (pressure of radiation)

* `art792_radiation_pressure` — **true but weaker in content than the prose suggests, and two of
  its hypotheses are never used**. `uE ⬝ᵥ uE = 1`, `E = √(E·E) • uE` (and the same for `H`) do not
  occur in the proof, and the fields enter only through `sq E`, `sq H`: the theorem is a statement
  about the *tension form* `tensionWithLateralPressure`, not about the stress of the field `E`. It
  therefore cannot distinguish `componentForm E` (tension `E²/8π`) from the Art. 111 dielectric
  stress (tension `K E²/8π`), which is exactly the content the prose claims.
  The sharpest form of this: the *whole* content of the theorem is the algebra of
  `tensionWithLateralPressure`. For any two numbers `p₁, p₂` and any directions `uE, uH ⊥ n`, the
  normal stress of the superposed stress is `−(p₁ + p₂)` (`art792_tautology`) — no field, energy
  density or article enters. Since `art792_radiation_pressure` sets `p₁ = K E²/8π`,
  `p₂ = μ H²/8π`, which *are* the energy densities, its conclusion is an identity in the tension
  parameters. What it does not do — derive the pressure from the stress of the fields — is what
  `art792_with_field_stress` supplies.
  I proved
  * `art792_radiation_pressure_weak`: the same conclusion with those four hypotheses dropped —
    so the stated hypotheses are redundant (not inconsistent: `E = uE = (1,0,0)` satisfies them);
  * `art792_with_field_stress`: with the stress **built from the fields** — `dielectricStress K E`
    plus the Art. 641 stress of `B = μH` — the pressure across a transverse front is
    `K E²/8π + H²/8π`, independent of `μ`;
  * `art792_energy_iff`: that pressure equals the whole energy
    `electrostaticEnergy631 E ((K/4π)E) + electrokineticEnergy636 (μH) H` **iff `μ = 1` or
    `H = 0`**. This extends the repository's `art642_vs_art792` (magnetic half alone) to the whole
    superposed stress, for every capacity `K`.
  * `art792_numeric`: `K = 2`, `μ = 3`, `E = (1,0,0)`, `H = (0,2,0)`, normal `(0,0,1)`:
    pressure `−3/4π` but energy `7/4π`; with `K = μ = 1` both are `5/8π`.
  So Art. 792's "pressure equals the energy" is true in the case Maxwell uses (Art. 643,
  `B = H`, `μ = 1`) and false for the magnetized stress otherwise — the repository says this, and
  the audit confirms it and locates it in the full superposed stress.

## 3. Not audited / still open

* The integrated statements (`art105_directAction` on boxes, `art631_energyInField`,
  `art635_electrokineticInField` ± decay) were not re-derived; only their pointwise inputs were
  audited. Their box/decay classes remain as narrow as the README says.
* `Art634KineticEnergy`, `Art616GaugeChoiceAvailable`, `Art617Uniqueness` (Statements.lean) are as
  open as documented; nothing here touches them.
* A patch adding `dielectricStress` (and `dielectricStress_art107`, `stressForce_dielectricStress`,
  `art111_force_dielectric`, `dielectricStress_K_one_force`) to
  `Maxwell/Treatise/ElectrostaticStress.lean` would close the Art. 111 gap in the library; it is
  left here as an untracked file (`Audit.lean`), not applied to the repository.
