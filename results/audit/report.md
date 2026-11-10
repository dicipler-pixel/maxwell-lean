# Audit of `maxwell-lean`

Jeromie Beasley, *Maxwell's own electromagnetism, in Lean* — commit `c4eff60`,
10 November 2026. Independent check requested as "is this solid?", plus a survey of where it
sits in current research. Everything below was run in this repository; every command is quoted
so it can be repeated.

---

## 1. Verdict

**Solid.** The library builds and kernel-checks under its own pin, all 85 proved declarations
depend only on `propext`, `Classical.choice` and `Quot.sound`, there is no `sorry`, `axiom` or
`native_decide` anywhere, and every claim the README makes about *what is proved* is backed by a
declaration that exists and says what the README says it says. The formulas were checked against
the page images of the 1873 edition, not only against OCR, and the conventions (Art. 641's
`P_hk`, Maxwell's `∇² = −Δ`, Gaussian units with explicit `4π`) are the printed ones.

The one substantive gap is the one the README already declares: the existence half of Art. 617's
vector potential and the linked Art. 616 gauge choice need the Newtonian potential, which Mathlib
does not have; and `Art634KineticEnergy` is a *shape*, not yet a statement — as written it is
refutable, and I refute it below in Lean so the gap is recorded rather than hidden.

Findings are in §4. None of them touch a proved theorem. Three are about wording, two about what
remains unverified, one is a real mathematical hole in an open target, and two are engineering.

---

## 2. What was run, and what it said

**2.1 The pinned harness, end to end.** Lean `4.36.0-rc2` (`b35cb10`), Mathlib
`1b1ccf4b088b32fa3f23f2de1127433254a81e1e` (9111 cached oleans fetched), `lake build`:

| Step | Command | Result |
|---|---|---|
| Build | `lake build` | exit 0; 22 warnings, **all** of the form "imports … which is designed for use with the module system" |
| Placeholder scan | `rg 'sorry\|admit\|native_decide\|^axiom '` over `Maxwell/`, `Maxwell.lean` | nothing |
| Axiom audit | `./scripts/check_axioms.sh` | `axiom audit passed: 85 theorems, standard axioms only` |
| Kernel replay | `lake env leanchecker Maxwell.<8 modules>` + `Maxwell.Statements` | all 9 replay clean |
| Declarations | `grep -cE '^(theorem\|lemma) '` | 86 (85 audited; the extra match is the word "theorem" at the start of a docstring line) |

So the four things the CI badge stands for do hold on this commit, reproduced here rather than
read off the badge.

**2.2 Portability.** The same sources, with a *proof-only* one-line change on 4.33.1 (see F6),
also compile against the system Mathlib (Lean 4.33.1) — all nine modules. The library is therefore
not tied to the rc pin in any deep way.

**2.3 The sources file.** `python3 scripts/check_sources.py` (added by this audit, §5) locates
each of the 24 quotations of `Maxwell/Sources.lean` in the Internet Archive OCR of the scan the
record names: **16 exact, 8 partial, 0 missing**. The partials are OCR damage, not misquotation:
`art111_energy` (a displayed formula OCR deleted), `art636`/`art645` (Fraktur `𝔅ℌ`, `𝔄`), `art590`
(`21` for `𝔄`), `art616` (`χ`), `art105_1881`, `art574_575`, `dyn1865_s57_58`. Every one of those
is legible on the page image.

**2.4 Printed formulas checked against page images** (not OCR — this matters, the OCR of these
displays is unusable):

* **1873 vol. I, p. 129, Art. 108 eq. (6):** `p_xx = (1/8π)(X²−Y²−Z²)`, `p_xy = (1/8π)2XY = p_yx`,
  `p_xz = (1/8π)2XZ`, with `p = (1/8π)R²`. Matches `componentForm`, `componentForm_xx_xy` and
  `art107_tension_of_art111` exactly. (The printed book has a typo on the third line, `p_xx` for
  `p_xz`; the formalization rightly does not reproduce it.)
* **1873 vol. I, p. 134, Art. 111:** `p = ½ 𝔇 𝔈 = (1/8π) K 𝔈² = (2π/K) 𝔇²`. Matches
  `art111_energy_eq_tension`, including the `K ≠ 0` needed by the third member.
* **1873 vol. II, p. 254, Art. 641 eqs. (13)–(15):** `X = d/dx P_xx + d/dy P_yx + d/dz P_zx`,
  `L = P_yz − P_zy`, and all nine components with `P_hk = (1/4π)B_h H_k − δ_hk H²/8π`. Matches
  `stressForce`, `couple` and `magneticStress641` exactly, including the non-symmetry.
* **1873 vol. II, p. 391, Art. 792:** the two energies `K𝔈²/8π`, `μℌ²/8π`; "tension … `p` parallel
  to `x`, pressure `p` parallel to `y` and `z` (Art. 107)", "tension `p` parallel to `y`, pressure
  `p` parallel to `x` and `z` (Art. 643)", "a pressure equal to `2p` in the direction of
  propagation … `2p` also expresses the whole energy in unit of volume". Matches
  `art792_radiation_pressure` and `art792_radiation_pressure_components`.
* **1873 vol. II, pp. 255–258, Arts. 642–645:** the bisector stress (17) and its four components,
  the `ε = 0` case (18), `𝔅 = ℌ` for Art. 643, "(Equations of Electromagnetic Force.) (20)",
  eq. (21) `div H = 0`, eq. (22) `X = vγ − wβ`, and the Art. 645 paragraph on p. 258. All match.
  The Article/page numbering in the README's table is right.

**2.5 Two claims I could **not** verify.** See F4.

---

## 3. The mathematics, re-derived independently

I re-derived the load-bearing identities by hand and (for the one that looked wrong at first)
numerically, then compared with the Lean statements:

* Art. 641's force law. `∂_h P_hk = (div B)H_k/4π + [(B·∇)H_k − (H·∂_k H)]/4π`; with `div B = 0`,
  `B = H + 4πI` and `curl H = 4πJ` this is `∇(I·H) + J × B` — Maxwell's printed
  `A dα/dx + B dβ/dx + C dγ/dx + vc − wb` — and equally `(I·∇)H + J × H`, the modern form. Both
  are true, and `art641_force` states the printed one with exactly the hypotheses (Arts. 400, 607,
  403) that Maxwell uses. I checked the identity on a concrete non-uniform example
  (`H = (y,0,0)`, `I = (0,1,0)`): both forms give `(1, −y/4π, 0)`, and the stress divergence agrees.
* Art. 642's bisector decomposition, Art. 643's `mH + J×H`, Art. 644's reduction, Art. 645's
  superposition: signs and the `4π` all consistent with the printed page.
* Art. 792: transverse `E`, `H` and any `K`, `μ` — the normal stress is minus the sum of the two
  energies; Maxwell's extra hypothesis `p₁ = p₂` (his eq. (8)) is genuinely unnecessary, and the
  repo's remark that Arts. 641–642 with `μ ≠ 1` give `H²/8π` rather than `μH²/8π` is correct.
* Arts. 631/635: both integrations by parts are right, and `½∭A·(curl H/4π) = (1/8π)∭B·H` needs no
  gauge condition on `A`.

---

## 4. Findings

**F1 (mathematical, open target — the only real hole).** `Art634KineticEnergy`
(`Maxwell/Statements.lean`) is not merely unproved, it is **false as written**: it quantifies over
`A`, `J`, the curves and the currents independently. Kernel-checked counterexample in
[`Refute634.lean`](Refute634.lean): one circuit up the `x` axis, constant `A = (1,0,0)`, `J = 0`,
current `1` — the left side is `½`, the right side `0`; `#print axioms` is standard too. The
README calls this "the shape of the claim", which is fair, but the next step is not a proof: it is
adding the link as a hypothesis (e.g. `J` as the divergence-free current of the circuits, or the
circulation/Stokes form). Fix: say "refutable without the circuit–current link (`Refute634.lean`)"
in the README row, or restate the target with the link.

**F2 (documentation).** README row for Art. 108: "the stress gives the force `ρR` on an element
(using Art. 77, no curl)". `art108_force` does take `hcurl : curl R x = 0` as an explicit
hypothesis (correctly — the field is a potential gradient), so "no curl" reads as if the theorem
needs none. Suggested wording: "using Art. 77, with `R` irrotational as his potential field is".

**F3 (documentation, minor).** `DESIGN.md` "Next steps" still lists the completed Art. 111 and
Art. 643 page-image confirmations as items 5 and 6 with strikethroughs; the list reads as if
`Art616GaugeChoiceAvailable` and the Art. 617 halves were the only things left, and now omits
F1. Housekeeping only.

**F4 (unverified).** Two claims in the docstrings rest on page images that I could not read from
the OCR and did not fetch: (i) that the 1873 printing of Art. 617 carries `1/μ` in front of the
integral (the equation `∇²𝔄 = 4πμℭ` on p. 236 is legible and has `μ`); (ii) that the
`χ = (1/4π)∭J/r` form is the 1892 third edition's. The 1873 p. 236 display itself is deleted by
the OCR, so these need the page image (`electricandmagne02maxwrich`, leaf `n285`–`n286`) or a
comparison copy of the 3rd edition. Not defects — just not confirmed here.

**F5 (scholarly, worth a citation).** The docstring for Arts. 598–599 says the electromotive
intensity "is not yet the later Heaviside–Lorentz force law on a point charge". That hedge is
defensible, but A. D. Yaghjian, *Reflections on Maxwell's Treatise*, PIER **149** (2014) 217–249,
§6.1, argues from the printed text that Maxwell *did* derive the general Faraday law for moving
circuits and hence `E + v × B` per unit moving charge. `emf598` already proves exactly that
vector; the honest move is to state the two readings and cite him, rather than to leave the
impression that Maxwell stopped short. Art. 599's `art599_motional` is the right lemma for it.

**F6 (engineering, tiny).** One proof line is 4.33.1-incompatible: in `art106_principal`,
`dotProduct_self_eq_zero.mp h` does not resolve on 4.33.1. Replacing the three-line `have hsq` with
a componentwise `nlinarith` makes every module compile on both toolchains. Not urgent (the pin is
the contract), but it is the only thing standing between the library and "builds on stock
Mathlib".

**F7 (engineering, future-proofing).** All 22 build warnings are the module-system notices
(`consider adding 'module' to the start of this file`). The pinned Mathlib already expects
modules; adding a `module` header per file would silence them and cut import cost. Worth doing
before the next pin bump, not now — it changes the compilation model of every file.

**F8 (process).** `scripts/Axioms.lean` lists 85 theorems by hand. It is right today (85 audited,
86 declarations, the 86th being a docstring false positive), but nothing fails when a *new*
theorem is added and forgotten. A generated list — `#print axioms` over every declaration the
library exports, emitted by a script — would close that hole. This is the one place where the
harness can silently rot.

---

## 5. What this audit added to the tree

* [`Refute634.lean`](Refute634.lean) — the kernel-checked counterexample of F1.
* [`../../scripts/check_sources.py`](../../scripts/check_sources.py) — re-locates every quotation
  of `Maxwell/Sources.lean` in its Internet Archive scan (16 exact, 8 partial-OCR, 0 missing on
  this commit), `--strict` to fail on partials. Fidelity rule 1 in the README is now a check
  that can be run, not only a promise.
* One line in the README "Build" block pointing at it; `.scratch/` added to `.gitignore`.

The large build artefacts (`.lake/`, the 4.36 toolchain under `.scratch/elan`) are ignored.

---

## 6. Where this sits, November 2026

Searched today; the point of each item is what it implies for this repository.

* **Physlib (formerly PhysLean), `leanprover-community/physlib`** — the main Lean 4 physics
  library. Its electromagnetism: 38 files, SI units, covariant `F_μν`, Lagrangian/`IsExtrema` →
  Maxwell's equations, gauge transformations, boosts, plane waves, point particles, tempered
  distributions, plus an April 2026 commit adding the 3-D vector form
  (`Electromagnetism/ThreeDimension/MaxwellEquations.lean`). I listed the whole tree today: there
  is **no stress tensor, no radiation pressure, no force law on a magnetized body** (field
  energy appears only through the Lagrangian's `−(1/4μ₀)F²` term). Physlib formalises the modern
  field equations; this repository formalises the 1873 route to the forces, which nobody else has
  in Lean. They are complementary, and `DESIGN.md` is right to keep them separate.
* **Mathlib** contains no `Poynting`, no stress tensor, no radiation pressure (searched the
  installed source: zero hits). The Newtonian potential is still absent — which is exactly why
  Art. 616/617 is open here and not a defect of this repo.
* **Lanyon's verified Maxwell solvers** (Lean 4, ~15k lines, formally verified 1-D/2-D/3-D
  solvers for Maxwell and perfectly hyperbolic Maxwell) are the other end of the spectrum:
  numerical, end-to-end, SI. No overlap.
* **A. D. Yaghjian, "Reflections on Maxwell's Treatise", PIER 149 (2014) 217–249** — the best
  modern reading of what Maxwell actually did (works from the 1891 3rd edition). Independent
  confirmation of this repo's central choices: Maxwell "does not derive what we refer to today as
  Poynting's theorem"; Maxwell obtains the electrostatic and magnetostatic stress dyadics in Arts.
  105–106 and 641–642; the force on a magnetized current-carrying element is
  `μ₀[(M·∇)H + J × H]`, the same identity `art641_force` states in Maxwell's printed form. Worth
  citing in the README, and see F5.
* **Hon & Goldstein, "The Key to Maxwell's Theory of Electrodynamics (1873): A Productive
  Methodology", Annalen der Physik (2022)**; and the 2024 book chapter "Lagrange's Method and
  Lagrangian's Mechanism in Maxwell's *A Treatise on Electricity and Magnetism* (1873)". Both bear
  on exactly the point this repo insists on — that Maxwell's "electromagnetic momentum" is
  Lagrangian/generalized momentum (Arts. 578, 590, 604, 634), not a field momentum density. The
  repo's reading is the current scholarly one, and these are the citable sources for it.
* **K. T. McDonald's example notes** (Princeton) are useful for the Art. 792 reading: Maxwell
  argued radiation pressure from the stress tensor in Arts. 792–793 and did not associate it with
  field momentum; the momentum-density reading is J. J. Thomson/Heaviside/Poincaré/Abraham. The
  repo's "no field momentum density, no Poynting vector" is correct history.
* Nothing found anywhere — Lean, Isabelle, Coq, Mizar, or the history literature — that formalises
  a historical physics text article by article with page-level citation. As far as a search
  reaches, this is the first of its kind, and its fidelity discipline (quotes as data, limits kept
  visible, no later ideas attributed) is the part worth promoting beyond the proofs.

---

## 7. Not verified here

* GitHub Actions itself: I reproduced its four steps locally on the pinned toolchain and they
  pass, but I did not read the badge or the run logs.
* The 1873/1881/1892 printing differences of F4.
* Anything about the physical reading Maxwell's own text leaves open (that the stress is
  maintained by a medium, Art. 645; where the energy resides, Art. 631 vs 1865 §74). Those are
  recorded as claims and limits in `Maxwell/Sources.lean`, not proved, which is the right status.

---

## 8. What the swarm added (same day, after §1–§7 were written)

Six members worked the open ends in parallel; every submission was compiled by me under the pinned
toolchain and its axioms re-checked. All six are in [`../swarm/`](../swarm/README.md) with an
integration order. The three findings that change the body of this report:

* **F-numbered status change.** `Art617Uniqueness` is no longer open in its uniqueness half:
  `results/swarm/liouville/MaxwellLiouville.lean` proves the missing Liouville theorem on `ℝ³`
  (maximum principle with an `+εy₀²` perturbation, no mean value property needed), so
  `art617_solution_subsingleton` holds with no hypothesis on the current `C`, and the README's
  Art. 617 row should be rewritten as "uniqueness proved; existence open".
* **F1 sharpened.** `Art634KineticEnergy` is refuted twice, independently — my
  [`Refute634.lean`](Refute634.lean) and `results/swarm/art634/Art634Stokes.lean` — and the missing
  ingredient is identified as the wire hypothesis, not a lemma. The field half is now real
  mathematics: Stokes on rectangles in all three coordinate planes, with
  `circuitMomentum_rectPath2` connecting the repository's own `circuitMomentum` to the flux.
* **F6 confirmed three times.** Three agents working independently hit the same one-line blocker
  for building on stock Mathlib: `import Mathlib.LinearAlgebra.Matrix.DotProduct` in
  `Maxwell/Treatise/ElectrostaticStress.lean`.
* **One real improvement to the library.** Art. 111 attached its tension to a stress matrix only
  for `K = 1`; `results/swarm/audit/Audit.lean` supplies `dielectricStress K E` with the tension
  `½𝔇𝔈 = K E²/8π` for every `K`, the pressure across `E`, the force `(div 𝔇)·𝔼`, and the reduction
  to `art108_force` at `K = 1`.
* **Art. 105's region class is no longer just boxes**: finite unions of touching boxes,
  box-minus-box, and polycubes with holes, with the hypothesis weakened from global `C²` to
  `ContDiffAt ℝ 2` on the region. And `norm_vec3_eq_sup` — Lean's `‖·‖` on `Vec3` is the sup norm,
  so `1/‖x‖` is not the Newtonian kernel — is the trap any future fundamental solution must avoid.

Nothing in the swarm contradicted a proved theorem of the library. All six results have since been
landed in `Maxwell/` (mapping in [`../swarm/README.md`](../swarm/README.md)); after landing the
harness is green again — `lake build` completes, `scripts/check_axioms.sh` audits 284 theorems on
the three standard axioms, `leanchecker` replays all 14 modules — and the library now has 284
theorems to its name where it had 85.
