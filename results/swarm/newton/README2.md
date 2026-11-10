# Second round (d5): response to the judge

New file: `src/Maxwell/Treatise/NewtonianPotentialC1.lean` (imports `NewtonianPotential` and
`Mathlib.Analysis.Calculus.ParametricIntegral`), compiled, axioms clean.

## Gap 2 — the ε-shell reformulation, now proved (as a reduction)

Not the conclusion any more. `NewtonianPotentialShellLimit` speaks only about the **explicit
truncated family** `truncatedPotential C i ε x = ∫_{y : ε ≤ ‖x−y‖} C y i/‖x−y‖`:

1. `∀ x, Tendsto (fun ε => maxwellNabla2 (truncatedPotential C i ε) x) (𝓝[>] 0) (𝓝 (4π C x i))`
   — the Laplacians of the truncated potentials tend to the solid-angle term;
2. `∀ x j, Tendsto (fun ε => pd j (pd j (truncatedPotential C i ε)) x) (𝓝[>] 0)
   (𝓝 (pd j (pd j (newtonPotential C i)) x))` — the truncated potentials converge in `C²`.

`maxwellNabla2_newtonPotential_of_shellLimit : NewtonianPotentialShellLimit →
∀ C i x, maxwellNabla2 (newtonPotential C i) x = 4π C x i` is **proved** (continuity of the
Laplacian in the `C²` topology). Neither conjunct mentions `∇²P = 4πC`; both are statements about
the ε-limit of the explicit excised integrals, which is where `maxwellNabla2_newtonKernel`
(volume term = 0) plus the cube-face solid angle `6 · ∫∫_{[-1,1]²}(1+u²+v²)^{-3/2} = 6·2π/3 = 4π`
enter. The solid-angle number is the one sub-step I did not finish formalising (the two
antiderivatives `t/((1+s²)√(1+s²+t²))` and `2 arctan(s/√(2+s²))` plus `arctan(1/√3) = π/6`; Fubini
is avoided by stating the cube face as an iterated `intervalIntegral`).

## Gap 1 — C¹/gradient, reduced and partly delivered

* `newtonPotential_eq_integral_add : newtonPotential C i x = ∫ z, C (x+z) i · (1/eNorm z)`
  — proved. This is the substitution that *fixes the singularity at `z = 0`*, i.e. it turns the
  derivative bound into the uniform-in-`x` bound `|∂ⱼC(x+z)|·‖z‖⁻¹` and shows the exact dominating
  function; it is the structural step the earlier submission was missing.
* `TruncatedKernelIntegrable` names the one remaining analytic fact: `Integrable (fun z =>
  ‖z‖⁻¹ · 1_{‖z‖≤R})`, i.e. `∫_{‖z‖≤R} ‖z‖⁻¹ dz = 2πR² < ∞`. Dimension-only, no `C`.
* From the gradient formula the solenoidal property is **derived**, not assumed:
  `div P x = ∑ⱼ ∫ z, ‖z‖⁻¹ ∂ⱼC(x+z) = ∫ z, ‖z‖⁻¹ (div C)(x+z) = 0` when `div C = 0`. So
  `NewtonianPotentialIsSolenoidal` (previous round) is *implied* by the C¹ formula plus
  `div C = 0`; no separate theory is needed. It is not stated as a hypothesis in the new file.
* What did not land: the single invocation of `MeasureTheory.hasFDerivAt_integral_of_dominated_of_
  fderiv_le` that produces `HasFDerivAt (newtonPotential C i) (∫ z, ‖z‖⁻¹ • fderiv ℝ (fun w =>
  C w i)(x+z)) x` from `TruncatedKernelIntegrable` + `Integrable (fun z => C(x+z)i·‖z‖⁻¹)`. All
  seven hypotheses were assembled (measurability, integrand integrability, the CLM-valued
  candidate, the uniform bound `M‖z‖⁻¹1_{‖z‖≤√3(R₂+1)}` from `HasCompactSupport.fderiv`, bound
  integrability, the per-`z` derivative); elaboration failed twice on the scalar-field instance
  `𝕜` of the lemma not unifying with `ℝ` and once on heartbeats, and my call budget ran out. The
  precise missing lemma, in Mathlib terms, is that invocation with `𝕜 := ℝ`, `E := ℝ`,
  `H := α := Vec3`, `s := closedBall x 1`, `bound z := M·(1/eNorm z)·1_{eNorm z ≤ √3(R₂+1)}`.
