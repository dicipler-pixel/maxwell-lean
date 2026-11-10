# Art. 616 (`Art616GaugeChoiceAvailable`): what is proved, and exactly what is missing

Direction d6, member m5. Deliverable: `GaugeLinearFunctional.lean` (compiles under Lean 4.33.1 +
Mathlib 4.33.1, no `sorry`, axioms `propext, Classical.choice, Quot.sound`).

## The target

`Maxwell.Statements.Art616GaugeChoiceAvailable`:

```lean
∀ A : Vec3 → Vec3, ContDiff ℝ ⊤ A → HasCompactSupport A →
  ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, div (fun y => A y + grad χ y) x = 0
```

The repo already reduces the condition, pointwise, to Maxwell's Poisson equation
(`art616_gauge_iff_poisson`): with `∇² = −Δ` (Maxwell's sign),

`div (𝔄 + ∇χ) = 0  ↔  ∇²χ = div 𝔄`.

So the only obstruction is **existence** for the equation `∇²χ = J`; there is no side condition on
`χ` beyond `C²` (no decay or integrability is needed for the statement, which is why the statement
is true as given and cannot be refuted), and the solution is never unique (add any harmonic
function). The statement is not vacuous: `χ = 0` does not solve it for a general `𝔄`.

## What this direction proves

1. **Closed-form solution of Maxwell's Poisson equation for profile sources.**
   `maxwellNabla2_gaugeChi` (`∇² = −Δ`, Maxwell's sign):
   for `w ≠ 0`, if `G'' = g` on `ℝ` then
   `maxwellNabla2 (fun x => −G (x ⬝ᵥ w) / (w ⬝ᵥ w)) x = g (x ⬝ᵥ w)`
   for every `x`, with `χ` of class `C²` (`contDiff_gaugeChi`). The proof is the chain rule for
   `x ↦ G (x ⬝ᵥ w)` (`pd_comp_dotCLM`, built from `HasFDerivAt.comp` and the continuous linear
   functional `dotCLM w x = x ⬝ᵥ w`) plus `∑ᵢ wᵢwᵢ = w ⬝ᵥ w`.
   Symbolically checked with `sympy`: `χ = sin(x ⬝ᵥ w)/(w ⬝ᵥ w)` has `−Δχ = sin(x ⬝ᵥ w)` for a
   random `w`, i.e. `∇²χ = g(x ⬝ᵥ w)`.

2. **Superposition over a finite set of profiles** (`maxwellNabla2_finset_sum`,
   `exists_gauge_of_finset_dotProduct`): if `div 𝔄 x = ∑_k g_k (x ⬝ᵥ w_k)` with `w_k ≠ 0`,
   then `χ = −∑_k G_k (x ⬝ᵥ w_k)/(w_k ⬝ᵥ w_k)` is `C²` and `div (𝔄 + ∇χ) = 0` *everywhere*.
   No PDE existence theorem is invoked.

3. **Both directions of the reduction to Poisson's equation, at the level of the target `Prop`:**
   * `art616GaugeChoiceAvailable_of_poissonSolver`: if `∇²χ = J` is solvable for every smooth
     compactly supported `J` (`NewtonianPotentialSolver`), then `Art616GaugeChoiceAvailable`
     holds (uses `contDiff_div`, `hasCompactSupport_div`: `div` of a smooth compactly supported
     field is smooth with compact support).
   * `poisson_solvable_of_gaugeChoiceAvailable`: conversely, `Art616GaugeChoiceAvailable` gives
     `∇²χ = div 𝔄` solvable for every smooth compactly supported `𝔄`.
   So the target is *exactly* Poisson solvability on the image of `div` on compactly supported
   fields.

4. **Poisson's equation solved for a genuinely compactly supported smooth source.**
   `poisson_smoothTransition`: for `w ≠ 0`, `χ = −smoothTransition (x ⬝ᵥ w)/(w ⬝ᵥ w)` is `C²` and
   `∇²χ x = smoothTransition'' (x ⬝ᵥ w)`, where `smoothTransition''`
   (`hasCompactSupport_smoothTransition_deriv_deriv`) is smooth and compactly supported (supported
   in `[0,1]`). So the missing lemma `NewtonianPotentialSolver` is *not* vacuous: it holds for at
   least one non-trivial compactly supported source (a profile of a bump), with an explicit
   solution. The gap is a uniform construction for all `J`, i.e. the fundamental solution.

5. **A worked instance** (`gauge_example_linear`, `gaugeChi_linear`): `𝔄 y = (y ⬝ᵥ e₀) • e₀` has
   `div 𝔄 = 1`, and `χ = −(x ⬝ᵥ e₀)²/2` (which is what the general formula returns) makes
   `𝔄 + ∇χ = 0`.

## The exact missing lemma

```lean
def NewtonianPotentialSolver : Prop :=
  ∀ J : Vec3 → ℝ, ContDiff ℝ ⊤ J → HasCompactSupport J →
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, maxwellNabla2 χ x = J x
```

i.e. Maxwell's Art. 616 eqs. (5)–(7), the Newtonian potential `χ = (1/4π)∭ J/r`: the fundamental
solution of the Laplacian in `ℝ³`. What a proof must supply, in order:

* `Δ(1/‖x‖) = 0` for `x ≠ 0` — an explicit computation (feasible: `pdᵢ(1/‖·‖) = −xᵢ/‖x‖³`,
  `pdᵢpdᵢ = −1/‖x‖³ + 3xᵢ²/‖x‖⁵`, sum `= 0`; `‖x‖² = ∑ xᵢ²` makes this polynomial bookkeeping).
* the *singular* part: `Δ(1/‖x − y‖)` is not integrable in `y` near `y = x`, so differentiating
  under the integral sign twice in `x` cannot be justified by dominated convergence
  (`∫_{B(x,ε)} ‖x−y‖^{-2} dy = ∞` in `ℝ³`). The classical route cuts the singularity out and
  evaluates the flux through the sphere `‖x − y‖ = ε`, which needs a **surface measure and a
  divergence theorem on spheres/balls**; Mathlib 4.33.1 has the divergence theorem for the whole
  space (`∫ div = 0`, compact support) and for boxes, and `MeasureTheory.Measure.addHaar_ball`,
  but no Stokes/divergence theorem on `∂B(x,ε)` and no coarea formula, so the flux computation
  `∮_{∂B(x,ε)} ∂_ν(1/‖·−x‖) dS = −4π` has to be built from scratch (or replaced by a
  weak-derivative / test-function argument, which needs distribution theory that Mathlib also
  lacks).

## Honest status of the class covered in (1)–(2)

A field of the form `𝔄 y = f (y ⬝ᵥ w) • v` with `f` compactly supported is **not** compactly
supported: `supp 𝔄 = {y : f (y ⬝ᵥ w) ≠ 0}` is the preimage of a bounded non-empty set under a
surjective linear functional, i.e. an unbounded slab. Also, if `𝔄` is `C¹` with compact support
then `∫ div 𝔄 = 0`, so `div 𝔄 = g (x ⬝ᵥ w)` forces `∫ g = 0`. The profile class is
*complementary* to the compactly supported class rather than a sub-case of it.
So (1)–(2) do not discharge `Art616GaugeChoiceAvailable`; they solve Maxwell's Poisson equation
in closed form for a non-trivial class of (non-compactly-supported) sources and isolate the
compact-support case as precisely the Newtonian-potential problem.

## How to compile

The repo does **not** compile under Lean 4.33.1 as it stands:
`Maxwell/Treatise/ElectrostaticStress.lean:338` uses `dotProduct_self_eq_zero.mp`, which does not
exist in Mathlib 4.33.1 (the repo pins 4.36.0-rc2). With that one proof replaced (e.g. by
`nlinarith [sq_eq E]` + `Fin` case bash) the whole repo compiles under 4.33.1. In this directory
I keep the patched copy and its oleans in `.scratch/repo/` and `.scratch/olean/`; the delivered
file is compiled with

```bash
cd .ultramath/smwatx3t5/m5/.scratch/repo &&
LEAN_PATH="$PWD/../olean:$PWD:$LEAN_PATH" lean ../../GaugeLinearFunctional.lean
```

(`import Maxwell.Statements` resolves against the patched copy; the file itself imports only
`Maxwell.Statements`, so it applies unchanged to the real repo once the repo's own toolchain is
available.)
