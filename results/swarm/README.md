# Swarm results, 10 November 2026

Six agents worked the open ends of this library for about seventy minutes, each on a separate
direction, and every submission was checked here before acceptance: compiled by me (not by the
author) under the pinned toolchain where the file already builds there, `#print axioms` re-run
by me, and the mathematics re-derived by hand or recomputed numerically. All six were accepted;
each file is no-`sorry`, and every theorem in them depends only on `propext`,
`Classical.choice`, `Quot.sound`.

**Landed.** Every result below now lives in the library (see the mapping at the end); the files
here are the agents' originals, kept as the audit trail, and some of them still carry the 4.33.1
spellings that had to be adapted for the pinned toolchain. The working copies, with build scripts
and per-agent notes, are under `.ultramath/smwatx3t5/`.

After landing: `lake build` green, `scripts/check_axioms.sh` audits **284** theorems (`propext`,
`Classical.choice`, `Quot.sound` only), `leanchecker` replays all 14 modules, and
`scripts/check_sources.py` still locates all 24 quotations.

| Directory | Direction | Status |
|---|---|---|
| `liouville/` | Art. 617 uniqueness | **closes** the repo's remaining hypothesis |
| `audit/` | statement audit of the stress/energy theorems | findings + the missing dielectric stress |
| `art634/` | Art. 634, the field side | Stokes on rectangles; target refuted as stated |
| `gauge/` | Art. 616 gauge choice | closed form for profile sources; exact reduction |
| `boxes/` | Art. 105 beyond one box | polycubes with holes; local hypotheses |
| `newton/` | Art. 616/617 existence | kernel and reduction; the singular integral still open |

---

## 1. `liouville/MaxwellLiouville.lean` — Art. 617 uniqueness is closed

`Maxwell.liouville_maxwellNabla2` has exactly the type of the hypothesis `hL` that
`Maxwell.Treatise.VectorPotential.art617_unique_of_liouville` was carrying, so
`art617_uniqueness` and `art617_solution_subsingleton` now hold outright. Consequences:

* `art617_solution_subsingleton μ C` — at most one solution of the Art. 617 system, with **no**
  hypothesis on the current `C` (not smooth, not compactly supported, not solenoidal).
* `art617Uniqueness_of_exists` — `Maxwell.Statements.Art617Uniqueness` follows from the
  existence half alone. That is the correct status of the repo's open target now.
* `art617_existsUnique_zero` — the full `∃!` in the case `μ = 0`.
* `not_tendsto_coord`, `maxwellNabla2_coord` — the decay hypothesis is not decorative: the
  coordinate functions are `∇²`-harmonic and do not decay.

Method, since it matters for reuse: Mathlib 4.33.1 has no maximum principle for harmonic
functions on `ℝⁿ` and no mean value property, and `Fin 3 → ℝ` has no `InnerProductSpace`
instance (so `Δ` is unusable). The file builds the second-derivative test at an interior maximum
(Mathlib has only the converse), gets `0 ≤ ∇²f` there for Maxwell's sign convention, proves the
weak maximum principle on a ball, and takes the radius to infinity with a `+εy₀²` perturbation
(`∇²` drops by `2ε`, and `∇²(y₀²) = −2` is the perturbation's sign). Compiles on the pinned
toolchain, 3.0 s.

## 2. `audit/Audit.lean` + `AuditFindings.md` — the stress theorems are sound

52 theorems. The load-bearing stress/energy declarations were checked three ways: a model
satisfying every hypothesis with a nonzero conclusion (non-vacuity), a counterexample for each
hypothesis (is it load-bearing), and exact rational evaluations of the printed formulas.

* `art641_force` — **Art. 403 is load-bearing**: with `B = H = id`, `I = J = 0` every other
  hypothesis holds and the conclusion fails. So the theorem is exactly as strong as Maxwell's own
  use of `div B = 0` in Art. 640 eq. (8).
* `art792_radiation_pressure` — true, but its four direction/unit hypotheses are unused, and its
  content is the tension-form algebra; `art792_tautology` says so, and
  `art792_with_field_stress` / `art792_energy_iff` supply the field-stress version and the
  `μ = 1` condition.
* `art111_energy_eq_tension` — the numbers are right, `hK` is redundant under Lean's total
  division, **and the library attached the tension to a stress matrix only for `K = 1`**. The
  repair is here: `dielectricStress K E = K • componentForm E`, with
  `dielectricStress_art107` (tension = `½𝔇𝔈 = K E²/8π` for every `K`), `dielectricStress_pressure`,
  `stressForce_dielectricStress` / `art111_force_dielectric` (force `(div 𝔇)·𝔈`) and
  `dielectricStress_K_one_force` (K = 1 recovers `art108_force`).

This is the one part of the swarm that improves the library rather than extending it.

## 3. `art634/` — Stokes on rectangles, and the target refuted

`art591_stokes_rect0/1/2`: circulation of `𝔄` round a rectangle = flux of `curl 𝔄` through it,
in all three coordinate planes, from Green's theorem on a rectangle
(`integral2_divergence_prod_of_hasFDerivAt`) with the orientation checked by hand. The curl
identification is not assumed — `curl_zero/one/two` discharge it. `art591_stokes_L2` gives
L-shaped hexagons; `div_curl_eq_zero` and `boxFlux_curl_eq_zero` make the circuit momentum
independent of the spanning surface, which is what Art. 590 presupposes.

`circuitMomentum_rectPath2` and `art634_single_circuit` connect the repository's own
`circuitMomentum` to the flux. `art634_shape_needs_wire_hypothesis` refutes
`Art634KineticEnergy` as stated — independently of `results/audit/Refute634.lean`, which reaches
the same conclusion another way. The remaining gap is stated exactly: `J` is a function while a
circuit's current lives on a curve, so the identity needs a distributional current or a thin-wire
limit (tubular neighbourhood + dominated convergence), neither of which Mathlib has.

## 4. `gauge/GaugeLinearFunctional.lean` — Art. 616 in closed form, and the exact reduction

For sources `div A = g(x·w)`, `χ = −G(x·w)/(w·w)` with `G'' = g` satisfies
`∇²χ = g(x·w)` in Maxwell's sign and `div(A + ∇χ) = 0`. Then
`art616GaugeChoiceAvailable_of_poissonSolver` and `poisson_solvable_of_gaugeChoiceAvailable`
pin the open target to Poisson solvability on the image of `div` — the converse is stated for
that image, which is what makes it true and is the useful half.

Correction from the agent, which is right: a source `g(x·w)` is never compactly supported unless
trivial, so this family is a slab, not a member of the target class; `gauge_example_linear` is
non-vacuous but in the slab class. `Art616GaugeChoiceAvailable` therefore stays open.

## 5. `boxes/BoxComplex.lean` — Art. 105 beyond a single box

The divergence theorem on finite unions of boxes (touching allowed, null intersections),
box-minus-inner-box, and polycubes with holes; `AccountedForByStress` and Art. 105 lifted onto
those regions. The hypothesis is weakened from global `C²` + Poisson everywhere to
`IsStressPotentialOn` (C² at points of the region, Poisson there, ρ continuous there) — the local
content of Art. 105. Strictness is discharged, not asserted: `staircase_not_box` exhibits a point
of the enclosing box outside the staircase region, and `art105_planeKernel_box` uses `Ψ = 1/x₀`,
which is not globally `C²`.

Carry this forward: `norm_vec3_eq_sup` — Lean's `‖·‖` on `Vec3` is the **sup** norm, so `1/‖x‖`
is not the Newtonian kernel. `RadiationPressure.lean` already uses `√(sq v)` for this reason, and
any fundamental solution must too (`newton/newton` uses `eNorm = √(sq ·)`).

Not delivered from that direction: differentiability only off a countable exceptional set.

## 6. `newton/` — Art. 616/617 existence: kernel proved, singular integral reduced

Round 1 proved the general power law `maxwellNabla2 (fun y => (sq y)^p) x = −(4p²+2p)(sq x)^(p−1)`
(checked by hand), hence `maxwellNabla2_newtonKernel`: `1/|x−y|` is `∇²`-harmonic off the source;
the decay `newtonPotential_tendsto_zero`; and the μ-scaled assembly `art617_existence_of_poisson`.

Round 2 replaced the assumed conclusion with a genuine reduction:
`newtonPotential_eq_integral_add` (the substitution `y = x + z`, singularity at the origin) and
`NewtonianPotentialShellLimit`, which asks only that the **truncated** potentials `P_ε` converge
in `C²` to `P` and that their Laplacians converge to `4πC`; `maxwellNabla2_newtonPotential_of_shellLimit`
derives `∇²P = 4πC`. I checked the cube-face constant numerically:
`∫∫_{[-1,1]²}(1+u²+v²)^{-3/2} = 2π/3`, six faces `= 4π`, and the ε-scaling reduces to it.

**Art. 617 existence is still open.** What remains is four named items, all standard:
`TruncatedKernelIntegrable` (true; `∫_{|z|≤R}|z|⁻¹ = 2πR²`), the single
`hasFDerivAt_integral_of_dominated_of_fderiv_le` invocation that did not elaborate (the
"scalar field vs ℝ" mismatch is the CLM step: apply it to the ℝ-valued integrand, then apply the
resulting `ContinuousLinearMap` to a direction), and the two conjuncts of the shell limit
(the C²-convergence, and the Laplacian limit whose only hard ingredient is the cube-face
integral). Solenoidality is a derivation in principle, not yet a theorem: with the gradient
formula, `div P = ∫ |z|⁻¹ div C(x+z) = 0`, but the gradient formula is exactly what did not land,
so `NewtonianPotentialIsSolenoidal` remains an assumption in `art617_existence_of_poisson`.

---

## Landing order, if these are to be merged

1. `import Mathlib.LinearAlgebra.Matrix.DotProduct` in `Maxwell/Treatise/ElectrostaticStress.lean`
   — three agents hit this independently; it is the only thing keeping the library off stock
   Mathlib 4.33.1.
2. `liouville/` into `Maxwell/Treatise/VectorPotential.lean`; update the Art. 617 row of the
   README (uniqueness proved, existence open) and add the new theorems to `scripts/Axioms.lean`.
3. `audit/`'s `dielectricStress` into `ElectrostaticStress.lean`; extend the Art. 111 README row
   from `K = 1` to all `K`.
4. `art634/`'s Stokes and circuit theorems; rewrite the `Art634KineticEnergy` row around
   `circuitMomentum_rectPath2` and the wire hypothesis, citing `Refute634.lean`.
5. `boxes/` — replace "boxes only" with the polycube class in the README.
6. `gauge/` and `newton/` as new modules, with their remaining hypotheses stated as hypotheses.

Two files need a rename before they build on the pin (they build on 4.33.1, which is the
toolchain the swarm was told to use): `gauge/GaugeLinearFunctional.lean` (`Set.Ioi` membership
drift at lines 338 and 341) and `newton/NewtonianPotentialC1.lean` (`tendsto_finset_sum` →
`tendsto_finsetSum`).

---

## Where each file went

| Original | Landed as |
|---|---|
| `liouville/MaxwellLiouville.lean` | `Maxwell/Treatise/VectorPotential.lean` (section `Liouville`); `art617Uniqueness_of_exists` in `Maxwell/Statements.lean` |
| `audit/Audit.lean` | `dielectricStress` family in `Maxwell/Treatise/ElectrostaticStress.lean`; `art111_energy_eq_tension_all` there too. The counterexamples and rational evaluations stay in the audit file, not the library. |
| `art634/*.lean` | `Maxwell/Treatise/CircuitFlux.lean`; the refutation `art634_shape_needs_wire_hypothesis` in `Maxwell/Statements.lean` |
| `boxes/BoxComplex.lean` | `Maxwell/Treatise/BoxComplex.lean` (verbatim; `pd_coord`→`pd_coord_apply`, `pd_sq`→`pd_sq_apply` to avoid clashes) |
| `gauge/GaugeLinearFunctional.lean` | `Maxwell/Treatise/GaugeLinearFunctional.lean`; the two reductions in `Maxwell/Statements.lean`. **Fixed for the pin**: `Set.Ioi` membership lemmas rewritten, `tendsto_finset_sum`→`tendsto_finsetSum`. |
| `newton/NewtonianPotential.lean` | `Maxwell/Treatise/NewtonianPotential.lean` (imports extended for the `rpow` derivative lemmas on the pin) |
| `newton/NewtonianPotentialC1.lean` | `Maxwell/Treatise/NewtonianPotentialC1.lean`. **Fixed for the pin**: `tendsto_finsetSum`, `Mathlib.MeasureTheory.Group.Integral` import, `integral_sub_right_eq_self`. |
