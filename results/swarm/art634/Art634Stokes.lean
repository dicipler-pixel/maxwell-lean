/-
Copyright (c) 2026. Released under the MIT license (see LICENSE).
-/
import Maxwell.Statements
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Art. 634: Stokes' circulation identity for rectangular circuits

Treatise 1873, vol. II, Art. 634, eq. (16) (p. 248) writes the kinetic energy of the currents as
`T = ½ ∑ pᵢ iᵢ = ½ ∭ (Fu + Gv + Hw)`, with `pᵢ = ∮ 𝔄 · ds` the electromagnetic momentum of
circuit `i` (`Maxwell.circuitMomentum`, Arts. 590, 604) and `𝔄` the vector potential.

The two sides of `Maxwell.Statements.Art634KineticEnergy` are integrals over different objects:
a finite sum of line integrals over loops `γᵢ`, and a volume integral against a current density
`J : Vec3 → Vec3`.  The step that lets one be converted into the other is Stokes' theorem on a
surface spanning each circuit.  This file proves that step for the class of surfaces Mathlib
4.33.1 supports exactly — planar rectangles in a coordinate plane — with the normal of the
right-handed cyclic orientation:

`∮_{∂R} 𝔄 · ds = ∫_R (curl 𝔄) · n dS`.

So (Art. 591, `𝔅 = curl 𝔄`) the momentum of a rectangular circuit is the induction flux through
it, which is the field-side half of Art. 634.
-/

namespace Maxwell

open Matrix MeasureTheory
open scoped Interval

/-! ## The three coordinate planes, with right-handed surface coordinates

For the plane `x_k = e` the surface coordinates `(s, t)` are chosen cyclically,
`(s, t) = (k+1, k+2)` mod 3, so that `e_s × e_t = e_k`, and the flux integral of the `k`-th
component of the curl equals the circulation in the positive sense about `e_k`. -/

/-- The linear map `(s, t) ↦ s • e_s + t • e_t`, used as the derivative of each plane embedding. -/
noncomputable def planeCoord (s t : Fin 3) : (ℝ × ℝ) →L[ℝ] Vec3 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (axis s) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (axis t)

theorem planeCoord_apply (s t : Fin 3) (q : ℝ × ℝ) :
    planeCoord s t q = q.1 • axis s + q.2 • axis t := rfl

@[simp] theorem planeCoord_one_zero (s t : Fin 3) : planeCoord s t (1, 0) = axis s := by
  rw [planeCoord_apply]; simp

@[simp] theorem planeCoord_zero_one (s t : Fin 3) : planeCoord s t (0, 1) = axis t := by
  rw [planeCoord_apply]; simp

/-- The point of the plane `x₀ = e` with surface coordinates `(x₁, x₂) = (s, t)`. -/
noncomputable def pt0 (e : ℝ) (q : ℝ × ℝ) : Vec3 := q.1 • axis 1 + q.2 • axis 2 + e • axis 0

/-- The point of the plane `x₁ = e` with surface coordinates `(x₂, x₀) = (s, t)`. -/
noncomputable def pt1 (e : ℝ) (q : ℝ × ℝ) : Vec3 := q.1 • axis 2 + q.2 • axis 0 + e • axis 1

/-- The point of the plane `x₂ = e` with surface coordinates `(x₀, x₁) = (s, t)`. -/
noncomputable def pt2 (e : ℝ) (q : ℝ × ℝ) : Vec3 := q.1 • axis 0 + q.2 • axis 1 + e • axis 2

theorem hasFDerivAt_pt0 (e : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (pt0 e) (planeCoord 1 2) p := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => planeCoord 1 2 q + e • axis 0)
      (planeCoord 1 2) p := (planeCoord 1 2).hasFDerivAt.add_const _
  simpa [pt0, planeCoord_apply] using h

theorem hasFDerivAt_pt1 (e : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (pt1 e) (planeCoord 2 0) p := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => planeCoord 2 0 q + e • axis 1)
      (planeCoord 2 0) p := (planeCoord 2 0).hasFDerivAt.add_const _
  simpa [pt1, planeCoord_apply] using h

theorem hasFDerivAt_pt2 (e : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (pt2 e) (planeCoord 0 1) p := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => planeCoord 0 1 q + e • axis 2)
      (planeCoord 0 1) p := (planeCoord 0 1).hasFDerivAt.add_const _
  simpa [pt2, planeCoord_apply] using h

theorem continuous_pt0 (e : ℝ) : Continuous (pt0 e) :=
  (planeCoord 1 2).continuous.add continuous_const

theorem continuous_pt1 (e : ℝ) : Continuous (pt1 e) :=
  (planeCoord 2 0).continuous.add continuous_const

theorem continuous_pt2 (e : ℝ) : Continuous (pt2 e) :=
  (planeCoord 0 1).continuous.add continuous_const

/-! ## Surface and circuit integrals for a rectangle -/

/-- Flux of the induction `𝔅 = curl 𝔄` through the rectangle `[a,b] × [c,d]` of the plane
`x₂ = e`, with normal `+e₂`. -/
noncomputable def rectFlux2 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in c..d, curl A (pt2 e (x, y)) 2

/-- Circulation of `𝔄` round the boundary of the same rectangle, taken counterclockwise seen
from `+e₂`: `(a,c) → (b,c) → (b,d) → (a,d) → (a,c)`. -/
noncomputable def rectCirc2 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  (∫ x in a..b, A (pt2 e (x, c)) 0) + (∫ y in c..d, A (pt2 e (b, y)) 1) -
    (∫ x in a..b, A (pt2 e (x, d)) 0) - (∫ y in c..d, A (pt2 e (a, y)) 1)

/-- Flux of `𝔅` through the rectangle `[a,b] × [c,d]` (in `(x₂, x₀)`) of the plane `x₁ = e`,
with normal `+e₁`. -/
noncomputable def rectFlux1 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in c..d, curl A (pt1 e (x, y)) 1

/-- Circulation round the same rectangle, counterclockwise seen from `+e₁`. -/
noncomputable def rectCirc1 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  (∫ x in a..b, A (pt1 e (x, c)) 2) + (∫ y in c..d, A (pt1 e (b, y)) 0) -
    (∫ x in a..b, A (pt1 e (x, d)) 2) - (∫ y in c..d, A (pt1 e (a, y)) 0)

/-- Flux of `𝔅` through the rectangle `[a,b] × [c,d]` (in `(x₀, x₁)`) of the plane `x₀ = e`,
with normal `+e₀`. -/
noncomputable def rectFlux0 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in c..d, curl A (pt0 e (x, y)) 0

/-- Circulation round the same rectangle, counterclockwise seen from `+e₀`. -/
noncomputable def rectCirc0 (A : Vec3 → Vec3) (e a b c d : ℝ) : ℝ :=
  (∫ x in a..b, A (pt0 e (x, c)) 1) + (∫ y in c..d, A (pt0 e (b, y)) 2) -
    (∫ x in a..b, A (pt0 e (x, d)) 1) - (∫ y in c..d, A (pt0 e (a, y)) 2)

/-! ## The generic rectangle theorem -/

/-- **Stokes for a coordinate rectangle.**  For a plane embedding `φ` with derivative `L`, an axis
`k` whose curl component is `∂_s 𝔄_t − ∂_t 𝔄_s` in the cyclic pair `(s,t)`, with `L (1,0) = e_s`
and `L (0,1) = e_t`, the flux of `curl 𝔄` through the rectangle equals the circulation round its
boundary.  This is `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt` (Green's theorem on
`[a,b] × [c,d]`) applied to the components `(𝔄_t, −𝔄_s)`. -/
theorem stokes_rect_gen {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A)
    {s t k : Fin 3} {φ : ℝ × ℝ → Vec3} {L : (ℝ × ℝ) →L[ℝ] Vec3}
    (hφc : Continuous φ) (hφd : ∀ p, HasFDerivAt φ L p)
    (hL₀ : L (1, 0) = axis s) (hL₁ : L (0, 1) = axis t)
    (hcurl : ∀ x, curl A x k = pd s (fun z => A z t) x - pd t (fun z => A z s) x)
    (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, curl A (φ (x, y)) k) =
      (((∫ x in a..b, -(A (φ (x, d)) s)) - ∫ x in a..b, -(A (φ (x, c)) s)) +
          ∫ y in c..d, A (φ (b, y)) t) -
        ∫ y in c..d, A (φ (a, y)) t := by
  have hdt : Differentiable ℝ (fun z => A z t) :=
    (contDiff_pi.1 hA t).differentiable (by norm_num)
  have hds : Differentiable ℝ (fun z => A z s) :=
    (contDiff_pi.1 hA s).differentiable (by norm_num)
  have Hdf : ∀ p ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min c d) (max c d),
      HasFDerivAt (fun p : ℝ × ℝ => A (φ p) t)
        ((fderiv ℝ (fun z => A z t) (φ p)).comp L) p := by
    intro p _
    have h := (hdt (φ p)).hasFDerivAt.comp p (hφd p)
    simpa [Function.comp_def] using h
  have Hdg : ∀ p ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min c d) (max c d),
      HasFDerivAt (-(fun p : ℝ × ℝ => A (φ p) s))
        (-((fderiv ℝ (fun z => A z s) (φ p)).comp L)) p := by
    intro p _
    have h := (hds (φ p)).hasFDerivAt.comp p (hφd p)
    exact h.neg
  have hcomp : ∀ p : ℝ × ℝ,
      ((fderiv ℝ (fun z => A z t) (φ p)).comp L) (1, 0) +
          (-((fderiv ℝ (fun z => A z s) (φ p)).comp L)) (0, 1) = curl A (φ p) k := by
    intro p
    rw [hcurl]
    simp [ContinuousLinearMap.comp_apply, hL₀, hL₁, pd]
    ring
  have HcF : ContinuousOn (fun p : ℝ × ℝ => A (φ p) t) ([[a, b]] ×ˢ [[c, d]]) :=
    ((contDiff_pi.1 hA t).continuous.comp hφc).continuousOn
  have HcG : ContinuousOn (-(fun p : ℝ × ℝ => A (φ p) s)) ([[a, b]] ×ˢ [[c, d]]) :=
    ((contDiff_pi.1 hA s).continuous.comp hφc).neg.continuousOn
  have Hi : IntegrableOn (fun p : ℝ × ℝ =>
      ((fderiv ℝ (fun z => A z t) (φ p)).comp L) (1, 0) +
        (-((fderiv ℝ (fun z => A z s) (φ p)).comp L)) (0, 1))
      ([[a, b]] ×ˢ [[c, d]]) := by
    have heq : (fun p : ℝ × ℝ =>
        ((fderiv ℝ (fun z => A z t) (φ p)).comp L) (1, 0) +
          (-((fderiv ℝ (fun z => A z s) (φ p)).comp L)) (0, 1)) =
        fun p => curl A (φ p) k := funext hcomp
    rw [heq]
    exact ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
      (((continuous_apply k).comp ((continuous_curl hA).comp hφc)).continuousOn)
  have key := integral2_divergence_prod_of_hasFDerivAt (fun p : ℝ × ℝ => A (φ p) t)
    (-(fun p : ℝ × ℝ => A (φ p) s)) (fun p => (fderiv ℝ (fun z => A z t) (φ p)).comp L)
    (fun p => -((fderiv ℝ (fun z => A z s) (φ p)).comp L)) a c b d HcF HcG Hdf Hdg Hi
  have hflux : (∫ x in a..b, ∫ y in c..d, curl A (φ (x, y)) k) =
      ∫ x in a..b, ∫ y in c..d,
        ((fun p : ℝ × ℝ => (fderiv ℝ (fun z => A z t) (φ p)).comp L) (x, y)) (1, 0) +
          ((fun p : ℝ × ℝ => -((fderiv ℝ (fun z => A z s) (φ p)).comp L)) (x, y)) (0, 1) := by
    refine intervalIntegral.integral_congr fun x _ =>
      intervalIntegral.integral_congr fun y _ => (hcomp (x, y)).symm
  rw [hflux, key]
  simp only [Pi.neg_apply, intervalIntegral.integral_neg]

/-! ## The three planes -/

/-- `curl 𝔄` component `2`, in the cyclic pair `(0,1)`. -/
theorem curl_two (A : Vec3 → Vec3) (x : Vec3) :
    curl A x 2 = pd 0 (fun z => A z 1) x - pd 1 (fun z => A z 0) x := by
  simp [curl]

/-- `curl 𝔄` component `1`, in the cyclic pair `(2,0)`. -/
theorem curl_one (A : Vec3 → Vec3) (x : Vec3) :
    curl A x 1 = pd 2 (fun z => A z 0) x - pd 0 (fun z => A z 2) x := by
  simp [curl]

/-- `curl 𝔄` component `0`, in the cyclic pair `(1,2)`. -/
theorem curl_zero (A : Vec3 → Vec3) (x : Vec3) :
    curl A x 0 = pd 1 (fun z => A z 2) x - pd 2 (fun z => A z 1) x := by
  simp [curl]

/-- **Art. 591 with Stokes, plane `x₂ = e`.**  The flux of the induction through a rectangle in a
coordinate plane equals the circulation of the momentum round its boundary. -/
theorem art591_stokes_rect2 {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d : ℝ) :
    rectFlux2 A e a b c d = rectCirc2 A e a b c d := by
  simp only [rectFlux2, rectCirc2]
  rw [stokes_rect_gen (A := A) hA (s := 0) (t := 1) (k := 2)
    (φ := pt2 e) (L := planeCoord 0 1) (continuous_pt2 e) (hasFDerivAt_pt2 e)
    (planeCoord_one_zero 0 1) (planeCoord_zero_one 0 1) (curl_two A) a b c d]
  simp only [intervalIntegral.integral_neg]
  ring

/-- **Art. 591 with Stokes, plane `x₁ = e`.** -/
theorem art591_stokes_rect1 {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d : ℝ) :
    rectFlux1 A e a b c d = rectCirc1 A e a b c d := by
  simp only [rectFlux1, rectCirc1]
  rw [stokes_rect_gen (A := A) hA (s := 2) (t := 0) (k := 1)
    (φ := pt1 e) (L := planeCoord 2 0) (continuous_pt1 e) (hasFDerivAt_pt1 e)
    (planeCoord_one_zero 2 0) (planeCoord_zero_one 2 0) (curl_one A) a b c d]
  simp only [intervalIntegral.integral_neg]
  ring

/-- **Art. 591 with Stokes, plane `x₀ = e`.** -/
theorem art591_stokes_rect0 {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d : ℝ) :
    rectFlux0 A e a b c d = rectCirc0 A e a b c d := by
  simp only [rectFlux0, rectCirc0]
  rw [stokes_rect_gen (A := A) hA (s := 1) (t := 2) (k := 0)
    (φ := pt0 e) (L := planeCoord 1 2) (continuous_pt0 e) (hasFDerivAt_pt0 e)
    (planeCoord_one_zero 1 2) (planeCoord_zero_one 1 2) (curl_zero A) a b c d]
  simp only [intervalIntegral.integral_neg]
  ring


/-! ## Art. 634 as stated in `Maxwell.Statements` needs the wire hypothesis

`Maxwell.Statements.Art634KineticEnergy` relates two sides over *independent* data: the left side
depends only on `𝔄`, the loops `γᵢ` and the currents `iᵢ`; the right side only on `𝔄` and `J`.
Nothing in the statement says that `J` is the current distribution carried by the circuits `γᵢ`.
Without that link the equation is false, as the next theorem shows: a constant potential, zero
current density and a straight (open) path with unit current give `½` against `0`.

This is why Art. 634 cannot be closed from the hypotheses it is stated with: the missing
hypothesis is exactly "the loops `γᵢ` carry the current `J`", i.e. `J` is the (distributional)
sum `∑ iᵢ ∮_γᵢ δ`. -/

theorem axis_dot_axis_self (i : Fin 3) : axis i ⬝ᵥ axis i = 1 := by
  fin_cases i <;> simp [axis, dotProduct, Fin.sum_univ_three]

/-- **Art. 634's equation is refutable as stated.**  With `𝔄 = e₀` constant, the open path
`γ t = t e₀` and unit current, the momentum side is `½`, while with `J = 0` the current-density
side is `0`. -/
theorem art634_shape_needs_wire_hypothesis :
    ¬ Art634KineticEnergy (fun _ : Vec3 => axis 0) (fun _ => 0)
      (fun (_ : Unit) (t : ℝ) => t • axis 0) (fun (_ : Unit) (_ : ℝ) => axis 0)
      (fun (_ : Unit) => 1) := by
  have hcm : circuitMomentum (fun _ : Vec3 => axis 0) (fun t : ℝ => t • axis 0)
      (fun _ : ℝ => axis 0) = 1 := by
    simp [circuitMomentum, axis_dot_axis_self]
  intro h
  simp only [Art634KineticEnergy] at h
  have hJ : (∫ x : Vec3, (fun _ : Vec3 => axis 0) x ⬝ᵥ (fun _ => 0 : Vec3 → Vec3) x) = 0 := by
    simp
  rw [hJ, mul_zero] at h
  simp [hcm] at h

/-! ## A strictly larger class: L-shaped rectilinear regions

Two rectangles sharing part of a side: with `a ≤ b ≤ b'` and `c ≤ c' ≤ d` the region
`[a,b]×[c,d] ∪ [b,b']×[c',d]` (in the plane `x₂ = e`) is an L-shaped hexagon, not a rectangle.
Its boundary traverses six segments; the vertical segment `{b} × [c',d]` appears in the two
rectangle boundaries with opposite signs and cancels, which is the whole content of passing from
single rectangles to rectilinear polygonal regions. -/

/-- Circulation round the boundary of the L-shaped region `[a,b]×[c,d] ∪ [b,b']×[c',d]` in the
plane `x₂ = e`, oriented counterclockwise seen from `+e₂`: six side integrals. -/
noncomputable def lCirc2 (A : Vec3 → Vec3) (e a b b' c c' d : ℝ) : ℝ :=
  (∫ x in a..b, A (pt2 e (x, c)) 0) + (∫ y in c..c', A (pt2 e (b, y)) 1) +
      (∫ x in b..b', A (pt2 e (x, c')) 0) + (∫ y in c'..d, A (pt2 e (b', y)) 1) -
    (∫ x in a..b', A (pt2 e (x, d)) 0) - (∫ y in c..d, A (pt2 e (a, y)) 1)

/-- Flux of the induction through the same L-shaped region, as the sum of the two rectangles. -/
noncomputable def lFlux2 (A : Vec3 → Vec3) (e a b b' c c' d : ℝ) : ℝ :=
  rectFlux2 A e a b c d + rectFlux2 A e b b' c' d

/-- **Art. 591 with Stokes, L-shaped regions.**  The flux of the induction through an L-shaped
region equals the circulation of the momentum round its six-sided boundary.  Proof: Stokes on each
of the two rectangles (`art591_stokes_rect2`), additivity of the integral over adjacent intervals
on the two cut sides, and cancellation of the shared segment `{b} × [c',d]`. The identity needs no order on the six scalars: interval integrals are oriented, so it holds for
any `a, b, b', c, c', d`; the ordering `a ≤ b ≤ b'`, `c ≤ c' ≤ d` is what makes it a statement
about an L-shaped region. -/
theorem art591_stokes_L2 {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b b' c c' d : ℝ) :
    lFlux2 A e a b b' c c' d = lCirc2 A e a b b' c c' d := by
  have hcontA : Continuous A := hA.continuous
  have h1 : Continuous fun y : ℝ => A (pt2 e (b, y)) 1 := by
    have hp : Continuous fun y : ℝ => pt2 e (b, y) :=
      (continuous_pt2 e).comp (by continuity : Continuous fun y : ℝ => (b, y))
    exact (continuous_apply 1).comp (hcontA.comp hp)
  have h2 : Continuous fun x : ℝ => A (pt2 e (x, d)) 0 := by
    have hp : Continuous fun x : ℝ => pt2 e (x, d) :=
      (continuous_pt2 e).comp (by continuity : Continuous fun x : ℝ => (x, d))
    exact (continuous_apply 0).comp (hcontA.comp hp)
  have hadd1 : (∫ y in c..d, A (pt2 e (b, y)) 1) =
      (∫ y in c..c', A (pt2 e (b, y)) 1) + (∫ y in c'..d, A (pt2 e (b, y)) 1) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (h1.intervalIntegrable c c')
      (h1.intervalIntegrable c' d)]
  have hadd2 : (∫ x in a..b', A (pt2 e (x, d)) 0) =
      (∫ x in a..b, A (pt2 e (x, d)) 0) + (∫ x in b..b', A (pt2 e (x, d)) 0) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (h2.intervalIntegrable a b)
      (h2.intervalIntegrable b b')]
  simp only [lFlux2, lCirc2, rectFlux2]
  rw [show (∫ x in a..b, ∫ y in c..d, curl A (pt2 e (x, y)) 2) = rectCirc2 A e a b c d from
      art591_stokes_rect2 hA e a b c d,
    show (∫ x in b..b', ∫ y in c'..d, curl A (pt2 e (x, y)) 2) = rectCirc2 A e b b' c' d from
      art591_stokes_rect2 hA e b b' c' d]
  simp only [rectCirc2]
  rw [hadd1, hadd2]
  ring

/-! ## Corollary: a curl-free momentum has zero circulation (independence of the surface) -/

/-- If `curl 𝔄 = 0` (everywhere, in particular on the rectangle), the circulation round a
rectangular circuit vanishes: the momentum has no circulation, so the spanning surface can be
moved without changing `∮ 𝔄 · ds`.  This is Art. 598/616's "the added terms disappear" in the
field language. -/
theorem rectCirc2_eq_zero_of_curl_eq_zero {A : Vec3 → Vec3} (hA : ContDiff ℝ 1 A) (e a b c d : ℝ)
    (hcurl : ∀ x, curl A x = 0) : rectCirc2 A e a b c d = 0 := by
  rw [← art591_stokes_rect2 hA e a b c d]
  simp only [rectFlux2]
  simp only [hcurl]
  simp

end Maxwell
