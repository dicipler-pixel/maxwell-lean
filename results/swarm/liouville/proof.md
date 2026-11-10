# Art. 617 uniqueness via a Liouville theorem for Maxwell's `∇²` — proof document

Direction `d1` (swarm `smwatx3t5`, member `m1`). Lean file: `MaxwellLiouville.lean`
(443+ lines, no `sorry`, axioms `propext, Classical.choice, Quot.sound` only — see
`axioms.txt`).

## What is proved

Everything below is in `namespace Maxwell`, for `Vec3 := Fin 3 → ℝ` and

`maxwellNabla2 f x = −∑ᵢ ∂ᵢ∂ᵢ f(x)` (Maxwell's sign: his `∇² = −Δ`, so his Poisson equation
`∇²f = 4πρ` is the usual `Δf = −4πρ`).

1. `eq_zero_of_maxwellNabla2_eq_zero`
   `ContDiff ℝ 2 u → (∀ x, maxwellNabla2 u x = 0) → Tendsto u (cocompact Vec3) (𝓝 0) → u = 0`.
   This is *exactly* the hypothesis `hL` of the repo's `art617_unique_of_liouville`, so the repo's
   Liouville gap is closed. Equivalent form: `liouville_maxwellNabla2`.
2. `art617_uniqueness`, `art617_solution_subsingleton μ C` — the Art. 617 system
   (`C²`, `div 𝔄 = 0`, `∇²𝔄 = 4πμC` componentwise, `𝔄 → 0` at infinity) has **at most one**
   solution, with *no* hypothesis on `μ` or `C` (not smooth, not compactly supported, not
   `div C = 0`). Both come from (1) through the repo's `art617_unique_of_liouville`.
3. `art617Uniqueness_of_exists` — the open target `Maxwell.Statements.Art617Uniqueness`
   (`∃! A, …` for smooth compactly supported solenoidal `C`) follows from the **existence** half
   alone: given one solution per `(μ, C)`, (2) upgrades `∃` to `∃!`.
4. `art617_existsUnique_zero` — the full `∃!` statement for `μ = 0`, the unique solution being
   `𝔄 = 0` (this is the only case of the `∃!` reachable without the Newtonian potential).
5. Sharpness / non-vacuity:
   * `maxwellNabla2_coord`, `not_tendsto_coord`: the coordinate function `y ↦ y₀` is
     `∇²`-harmonic and does *not* tend to `0`, so the decay hypothesis in (1) is essential;
   * `exists_maxwellNabla2_neg`: the hypothesis `∇²f < 0` of the maximum principle is
     satisfiable (`f = y₀²`), so nothing is vacuous.

## The argument

Mathlib 4.33.1 has *no* maximum principle and *no* mean value property for `HarmonicOnNhd` on
`ℝⁿ`; its only Liouville theorem (`InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant`)
is for the complex plane. Moreover Mathlib's `Δ`, `HarmonicAt`, `HarmonicOnNhd` **cannot even be
applied to `Vec3 = Fin 3 → ℝ`**: that type carries the Pi (sup) norm and
`synthInstanceFailed: InnerProductSpace ℝ (Fin 3 → ℝ)` (checked in Lean 4.33.1), so there is no
Laplacian instance on it at all. That is a second, independent reason the chain is built here, in
terms of the repo's `maxwellNabla2`.

**Step 1 (second-derivative test, `deriv_deriv_nonpos_of_isLocalMax`).** For `C²` `g : ℝ → ℝ` with
a local maximum at `x`, `deriv (deriv g) x ≤ 0`. Mathlib only has the converse
(`isLocalMax_of_deriv_deriv_neg`). Proof: suppose `L = g''(x) > 0`. Since `g'(x) = 0` (Fermat,
`IsLocalMax.deriv_eq_zero`) and `g'` is differentiable at `x` with derivative `L`,
`(g'(y) − g'(x))/(y − x) → L`, so `g'(y)/(y − x) > 0` for `0 < |y − x| < δ`. Take
`t = x + δ/2`; Lagrange's mean value theorem (`exists_deriv_eq_slope`) gives
`c ∈ (x, t)` with `g'(c) = (g t − g x)/(t − x)`; here `c − x ∈ (0, δ)` hence `g'(c) > 0`, so
`g t > g x`, contradicting the local maximality for `|t − x| < δ`.

**Step 2 (multivariate form).** For `C²` `f` and a local maximum at `x`,
`fderiv ℝ (fderiv ℝ f) x v v ≤ 0` for every `v` (`second_deriv_nonpos_of_isLocalMax`):
restrict to the line `t ↦ f (x + t • v)`, whose derivative is `t ↦ fderiv ℝ f (x + t • v) v`
(`deriv_line`) and whose second derivative at `0` is `fderiv (fderiv f) x v v`
(`hasDerivAt_fderiv_line`, via `HasFDerivAt.clm_apply` applied to the constant `v`), then apply
Step 1. Summing over `v = axis i` and using the repo's `pd_pd`:

   `0 ≤ maxwellNabla2 f x` at every interior local maximum of a `C²` `f`
   (`maxwellNabla2_nonneg_of_isLocalMax`).

**Step 3 (the perturbation).** `maxwellNabla2 (y ↦ y₀²) = −2`
(`maxwellNabla2_coord_sq`), computed from `pd i (y ↦ y₀*y₀) x = 2 x₀ (if i = 0 then 1 else 0)`;
with linearity (`maxwellNabla2_add`, `maxwellNabla2_const_mul`) this gives

   `maxwellNabla2 (y ↦ u y + ε y₀²) z = maxwellNabla2 u z − 2ε`  (`maxwellNabla2_perturb`),

i.e. `Δ` is raised by `2ε` — the classical strictly subharmonic perturbation.

**Step 4 (weak maximum principle, `exists_max_on_sphere`).** Let `f` be `C²` with `∇²f < 0` on the
open ball of radius `R`, and `‖x‖ < R`. The closed ball is compact, so `f` attains a maximum at
some `y`; if `‖y‖ < R` then `y` is interior, the closed ball is a neighbourhood of `y`, so `y` is a
local maximum and Step 2 gives `0 ≤ ∇²f(y)`, contradicting `∇²f(y) < 0`. Hence `‖y‖ = R` and
`f x ≤ f y`.

**Step 5 (Liouville, `eq_zero_of_maxwellNabla2_eq_zero`).** Let `∇²u = 0`, `u → 0` at infinity.
Fix `x₀` and `δ > 0`. By decay (`Tendsto` + `Filter.mem_cocompact`), pick a compact `K` with
`|u| < δ/2` off `K`, then `R > ‖x₀‖` with `K ⊆ ball 0 R`; a point on the sphere `‖y‖ = R` is
therefore outside `K`. Choose `ε = δ / (4(1+R²))` — after `R`, so that `εR² ≤ δ/2` — and apply
Step 4 to `f = u + ε y₀²`, whose `∇²f = −2ε < 0` (Step 3):

   `u x₀ ≤ u x₀ + ε x₀₀² = f x₀ ≤ f y = u y + ε y₀² < δ/2 + ε R² ≤ δ`.

So `u x₀ ≤ δ` for every `δ > 0`, i.e. `u x₀ ≤ 0`; the same argument for `−u` (which is also
`C²`, `∇²`-harmonic and decaying) gives `−u x₀ ≤ 0`. Hence `u x₀ = 0`.

## Exact commands

The repo pins Lean 4.36.0-rc2, which is not installed; against 4.33.1 one repo file needs one
extra import (`Mathlib.LinearAlgebra.Matrix.DotProduct` for `dotProduct_self_eq_zero` at
`Maxwell/Treatise/ElectrostaticStress.lean:338`). I keep that patched copy in `patched/` and build
the module under its own name:

```bash
REPO=/workspace/nucleus/work/projects/p-c1e28406062a4279aca922483c0a99ab/repo
M=$REPO/.ultramath/smwatx3t5/m1 ; OL=$M/olean
export LEAN_PATH="$OL:$REPO:$LEAN_PATH"
# 1. dependencies (olean files are required; `lean` does not elaborate imports from source)
cd $REPO
lean -o $OL/Maxwell/Basic.olean Maxwell/Basic.lean
cd $M/patched && lean -o $OL/Maxwell/Treatise/ElectrostaticStress.olean Maxwell/Treatise/ElectrostaticStress.lean
cd $REPO
for m in Treatise/VectorPotential Sources Treatise/MagneticStress Treatise/Energy \
         Treatise/RadiationPressure Treatise/ElectromotiveForce Statements; do
  lean -o $OL/Maxwell/$m.olean Maxwell/$m.lean
done
# 2. the deliverable
cd $M && lean -o $OL/MaxwellLiouville.olean MaxwellLiouville.lean
# 3. axiom audit
cd $M && lean Axioms.lean          # output in axioms.txt
```

## What remains (not proved here)

* **Existence in Art. 617** (Art. 616 eqs. (5)–(7)): for smooth compactly supported `C` with
  `div C = 0` one must exhibit `A(x) = μ ∫ C(y)/‖x − y‖ dy` and show it is `C²`, decaying,
  solenoidal and `∇²A = 4πμC`. The precise missing lemma:

  > `newtonian_maxwellNabla2`: for `f : Vec3 → ℝ` of class `C²` with compact support and `x : Vec3`,
  > `maxwellNabla2 (fun x => ∫ y, f y / ‖x − y‖) x = fourPi * f x`.

  Its proof is the classical singular-integral computation: differentiate once under the integral
  (`Mathlib.Analysis.Calculus.ParametricIntegral`, bound `‖x−y‖⁻²`), then for the second derivative
  split at `‖x − y‖ = ε`, apply the divergence theorem on the shell `ε < ‖x−y‖ < R` (the box
  version is already in the repo as `integral_div_eq_zero_of_decay`), and show the sphere term
  tends to `4π f x`. Note `Δ(1/‖·‖) = −4π δ₀`, hence the sign in Maxwell's `∇²` convention.
  Applied componentwise to `C`, this gives the existence half, and `art617Uniqueness_of_exists`
  then yields `Maxwell.Statements.Art617Uniqueness`.

* Everything else in this file is *complete*: no gaps, no `sorry`, no weakened statement. In
  particular the uniqueness reduction `art617Uniqueness_of_exists` is not a weakening: it is the
  `∃!` statement of `Maxwell.Statements` with existence factored out.

## Note on the repo patch

`patched/Maxwell/Treatise/ElectrostaticStress.lean` is a byte-copy of the repo file plus one
import line, needed only because Mathlib 4.33.1 does not re-export
`Mathlib.LinearAlgebra.Matrix.DotProduct`. Nothing else in the repo is modified; all my work is
under `.ultramath/smwatx3t5/m1/`.

To promote the deliverable into the repo (not done, since the repo is not mine to change):

1. copy `MaxwellLiouville.lean` to `Maxwell/Treatise/Liouville.lean` (the module name is not
   referenced by anything, so `import Maxwell.Treatise.VectorPotential` / `Maxwell.Statements`
   resolve unchanged from inside the repo);
2. on Lean 4.36.0-rc2 (the pinned toolchain) that is the only change needed — the extra import in
   `ElectrostaticStress.lean` is a 4.33.1-only compatibility fix;
3. `Maxwell.lean` (root) does not import `Maxwell.Statements`; add
   `import Maxwell.Treatise.Liouville` there if the results should be part of the built library.
