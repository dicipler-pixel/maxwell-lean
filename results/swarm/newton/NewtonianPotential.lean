/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Statements

/-!
# The Newtonian potential (Treatise 1873, vol. II, Arts. 616–618): the singular kernel

Maxwell's `∇²` is minus the Laplacian, and his construction of the vector potential
(Art. 616 eqs. (5)–(7), Art. 617) is the Newtonian potential `𝔄 = μ ∭ C/r` with Euclidean `r`.
This file starts the analysis that Art. 616/617 need and that the repository leaves open:
the Euclidean kernel `1/‖x−y‖` and the fact that it is Maxwell-harmonic in `x` off the source.
-/

namespace Maxwell

open Matrix Filter Topology MeasureTheory

/-! ## The Euclidean norm on `Vec3`

`Vec3 = Fin 3 → ℝ` carries the sup norm in Mathlib (`‖(1,1,1)‖ = 1`, `‖(1,0,0)‖ = 1`), which is
*not* Maxwell's `r`. The Euclidean norm is `√(x²+y²+z²)`, built here from the repository's `sq`. -/

/-- Maxwell's Euclidean `r` on `Vec3`, as the square root of the repository's `sq`. -/
noncomputable def eNorm (x : Vec3) : ℝ := Real.sqrt (sq x)

/-- Euclidean distance `r` between two points of space. -/
noncomputable def eDist (x y : Vec3) : ℝ := eNorm (x - y)

/-- **The Newtonian kernel** `1/r` of Art. 616 eqs. (5)–(7): the potential at `x` of a unit
source at `s`. -/
noncomputable def newtonKernel (s x : Vec3) : ℝ := 1 / eDist x s

theorem eNorm_nonneg (x : Vec3) : 0 ≤ eNorm x := Real.sqrt_nonneg _

theorem sq_eq_zero_iff {x : Vec3} : sq x = 0 ↔ x = 0 := by
  simpa [sq] using Matrix.dotProduct_self_eq_zero (v := x)

theorem sq_pos_iff {x : Vec3} : 0 < sq x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    have h0 : sq x = 0 := by rw [hx]; simp [sq]
    rw [h0] at h; exact lt_irrefl 0 h
  · intro hx
    have hne : ¬ (sq x = 0) := fun h0 => hx (sq_eq_zero_iff.mp h0)
    rcases lt_or_eq_of_le (sq_nonneg' x) with h | h
    · exact h
    · exact absurd h.symm hne

theorem eNorm_pos_iff {x : Vec3} : 0 < eNorm x ↔ x ≠ 0 := by
  rw [eNorm, Real.sqrt_pos, sq_pos_iff]

theorem eNorm_eq_zero {x : Vec3} : eNorm x = 0 ↔ x = 0 := by
  have h := eNorm_pos_iff (x := x)
  have hnn := eNorm_nonneg x
  constructor
  · intro h0
    by_contra hx
    have h1 : 0 < eNorm x := h.mpr hx
    linarith
  · intro h0
    subst h0
    simp [eNorm, sq]

theorem sq_eNorm (x : Vec3) : eNorm x ^ 2 = sq x := by
  rw [eNorm, Real.sq_sqrt (sq_nonneg' x)]

theorem eNorm_ne_zero {x : Vec3} (h : x ≠ 0) : eNorm x ≠ 0 := fun h0 => h ((eNorm_eq_zero).mp h0)

theorem sq_coord_le (x : Vec3) (i : Fin 3) : x i ^ 2 ≤ sq x := by
  rw [sq_eq]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

theorem abs_coord_le_eNorm (x : Vec3) (i : Fin 3) : |x i| ≤ eNorm x := by
  have h1 : |x i| = Real.sqrt (x i ^ 2) := (Real.sqrt_sq_eq_abs (x i)).symm
  rw [h1, eNorm]
  exact Real.sqrt_le_sqrt (sq_coord_le x i)

theorem norm_le_eNorm (x : Vec3) : ‖x‖ ≤ eNorm x := by
  refine (pi_norm_le_iff_of_nonneg (eNorm_nonneg x)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_coord_le_eNorm x i


/-! ## Partial derivatives as derivatives of line restrictions

`pd i f x` is the derivative at `0` of `t ↦ f (x + t • eᵢ)`. This lets every computation below run
in one variable, with no bookkeeping of continuous linear maps. -/

section Lines

theorem differentiableAt_sq (x : Vec3) : DifferentiableAt ℝ sq x := by
  have h : sq = fun y : Vec3 => y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    funext y; rw [sq_eq]
  rw [h]; fun_prop

/-- The restriction of `sq` to the line `x + t • eᵢ` is a quadratic with leading coefficient `1`. -/
theorem sq_line (x : Vec3) (i : Fin 3) (t : ℝ) :
    sq (x + t • axis i) = sq x + 2 * t * x i + t ^ 2 := by
  simp only [sq, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, axis]
  fin_cases i <;> simp <;> ring

theorem line_apply (x : Vec3) (i : Fin 3) (t : ℝ) : (x + t • axis i) i = x i + t := by
  simp [axis]

/-- `pd i f x` is the derivative of the restriction of `f` to the line through `x` along `eᵢ`. -/
theorem pd_eq_deriv_line {f : Vec3 → ℝ} {x : Vec3} (i : Fin 3) (hf : DifferentiableAt ℝ f x) :
    pd i f x = deriv (fun t : ℝ => f (x + t • axis i)) 0 := by
  have hder : HasDerivAt (fun t : ℝ => x + t • axis i) (axis i) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (axis i) |>.const_add x
  have hpt : (fun t : ℝ => x + t • axis i) 0 = x := by simp
  have hf' : HasFDerivAt f (fderiv ℝ f x) ((fun t : ℝ => x + t • axis i) 0) := by
    simpa using hf.hasFDerivAt
  have h := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => x + t • axis i)
    (l := f) (l' := fderiv ℝ f x) (f' := axis i) (x := 0) hf' hder
  rw [pd]
  exact h.deriv.symm

theorem hasDerivAt_sq_line (x : Vec3) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => sq (x + t • axis i)) (2 * x i) 0 := by
  have key : HasDerivAt (fun t : ℝ => (t + x i) * (t + x i) + (sq x - (x i) ^ 2))
      (1 * (0 + x i) + (0 + x i) * 1) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t + x i) 1 0 := (hasDerivAt_id (0 : ℝ)).add_const (x i)
    exact (h1.mul h1).add_const (sq x - (x i) ^ 2)
  have hfun : (fun t : ℝ => sq (x + t • axis i)) =
      fun t => (t + x i) * (t + x i) + (sq x - (x i) ^ 2) := by
    funext t; rw [sq_line]; ring
  rw [hfun]
  have hv : 1 * (0 + x i) + (0 + x i) * 1 = 2 * x i := by ring
  rw [hv] at key
  exact key

theorem pd_sq (i : Fin 3) (x : Vec3) : pd i sq x = 2 * x i := by
  rw [pd_eq_deriv_line i (differentiableAt_sq x)]
  exact (hasDerivAt_sq_line x i).deriv

end Lines


/-! ## The Laplacian of a radial function `(sq ·)^p`

Maxwell's `∇²` is minus the Laplacian, so `maxwellNabla2 (sq ·)^p x = -(∂ₓ² + ∂_y² + ∂_z²)`. -/

section Radial

theorem differentiableAt_sq_rpow (p : ℝ) {x : Vec3} (hx : sq x ≠ 0) :
    DifferentiableAt ℝ (fun y : Vec3 => (sq y) ^ p) x :=
  ((Real.hasDerivAt_rpow_const (Or.inl hx)).comp_hasFDerivAt x
    (differentiableAt_sq x).hasFDerivAt).differentiableAt

theorem pd_sq_rpow (p : ℝ) {x : Vec3} (hx : sq x ≠ 0) (i : Fin 3) :
    pd i (fun y : Vec3 => (sq y) ^ p) x = p * (sq x) ^ (p - 1) * (2 * x i) := by
  rw [pd_eq_deriv_line i (differentiableAt_sq_rpow p hx)]
  have hU := hasDerivAt_sq_line x i
  rw [show (fun t : ℝ => (sq (x + t • axis i)) ^ p)
      = (fun u : ℝ => u ^ p) ∘ (fun t => sq (x + t • axis i)) from rfl]
  rw [deriv.scomp]
  · rw [hU.deriv, Real.deriv_rpow_const]
    simp only [smul_eq_mul]
    rw [show sq (x + (0 : ℝ) • axis i) = sq x from by simp]
    ring
  · rw [show sq (x + (0 : ℝ) • axis i) = sq x from by simp]
    exact (Real.hasDerivAt_rpow_const (Or.inl hx)).differentiableAt
  · exact hU.differentiableAt

theorem eventually_sq_pos {x : Vec3} (hx : 0 < sq x) : ∀ᶠ y in 𝓝 x, 0 < sq y :=
  (differentiableAt_sq x).continuousAt.eventually (lt_mem_nhds hx)

theorem pd_sq_rpow_eventuallyEq (p : ℝ) {x : Vec3} (hx : 0 < sq x) (i : Fin 3) :
    (fun y => pd i (fun z => (sq z) ^ p) y) =ᶠ[𝓝 x]
      fun y => p * (sq y) ^ (p - 1) * (2 * y i) := by
  filter_upwards [eventually_sq_pos hx] with y hy
  exact pd_sq_rpow p (ne_of_gt hy) i

theorem differentiableAt_pd_sq_rpow (p : ℝ) {x : Vec3} (hx : 0 < sq x) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => pd i (fun z => (sq z) ^ p) y) x := by
  refine (pd_sq_rpow_eventuallyEq p hx i).differentiableAt_iff.mpr ?_
  have h1 : DifferentiableAt ℝ (fun y : Vec3 => (sq y) ^ (p - 1)) x :=
    differentiableAt_sq_rpow (p - 1) (ne_of_gt hx)
  have h2 : DifferentiableAt ℝ (fun y : Vec3 => y i) x := by fun_prop
  have e : (fun y : Vec3 => p * (sq y) ^ (p - 1) * (2 * y i))
      = fun y => (fun z => p) y * ((sq y) ^ (p - 1) * ((fun z => (2 : ℝ)) y * (fun z => z i) y)) := by
    funext y; ring
  rw [e]
  exact (differentiableAt_const (c := p) (x := x)).mul
    (h1.mul ((differentiableAt_const (c := (2 : ℝ)) (x := x)).mul h2))

/-- The second partial derivative of `(sq ·)^p`, still with `pd` only. -/
theorem pd_pd_sq_rpow (p : ℝ) {x : Vec3} (hx : 0 < sq x) (i : Fin 3) :
    pd i (fun y => pd i (fun z => (sq z) ^ p) y) x
      = p * (p - 1) * (sq x) ^ (p - 2) * (2 * x i) ^ 2 + p * (sq x) ^ (p - 1) * 2 := by
  rw [pd_eq_deriv_line i (differentiableAt_pd_sq_rpow p hx i)]
  -- the integrand is the explicit formula on a neighbourhood of `0`
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < sq (x + t • axis i) := by
    have hcont : ContinuousAt (fun t : ℝ => sq (x + t • axis i)) 0 := by
      have hfun : (fun t : ℝ => sq (x + t • axis i)) = fun t => sq x + 2 * t * x i + t ^ 2 :=
        funext (sq_line x i)
      rw [hfun]
      fun_prop
    have h0 : (0 : ℝ) < (fun t : ℝ => sq (x + t • axis i)) 0 := by simpa using hx
    exact hcont.eventually (lt_mem_nhds h0)
  have heq : (fun t : ℝ => pd i (fun z => (sq z) ^ p) (x + t • axis i)) =ᶠ[𝓝 0]
      fun t => p * (sq (x + t • axis i)) ^ (p - 1) * (2 * x i + 2 * t) := by
    filter_upwards [hpos] with t ht
    rw [pd_sq_rpow p (ne_of_gt ht) i, line_apply]
    ring
  rw [heq.deriv_eq]
  -- differentiate the explicit expression with `HasDerivAt`
  have hU : HasDerivAt (fun t : ℝ => sq (x + t • axis i)) (2 * x i) 0 := hasDerivAt_sq_line x i
  have hA : HasDerivAt (fun t : ℝ => (sq (x + t • axis i)) ^ (p - 1))
      ((2 * x i) * ((p - 1) * (sq x) ^ (p - 1 - 1))) 0 := by
    have hφ : HasDerivAt (fun u : ℝ => u ^ (p - 1)) ((p - 1) * (sq x) ^ (p - 1 - 1)) (sq x) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
    have hs := HasDerivAt.scomp_of_eq (g₁ := fun u : ℝ => u ^ (p - 1))
      (g₁' := (p - 1) * (sq x) ^ (p - 1 - 1)) (h := fun t : ℝ => sq (x + t • axis i))
      (h' := 2 * x i) (x := 0) (y := sq x) hφ hU (by simp)
    simpa [Function.comp_def] using hs
  have hB : HasDerivAt (fun t : ℝ => 2 * x i + 2 * t) 2 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    have h' : HasDerivAt (fun t : ℝ => 2 * t) 2 0 := by simpa using h
    have := h'.const_add (2 * x i)
    simpa [add_comm] using this
  have hAB := hA.mul hB
  have hfin : HasDerivAt (fun t : ℝ => p * ((sq (x + t • axis i)) ^ (p - 1) * (2 * x i + 2 * t)))
      (p * (((2 * x i) * ((p - 1) * (sq x) ^ (p - 1 - 1))) * (2 * x i + 2 * 0)
        + (sq x) ^ (p - 1) * 2)) 0 := by
    have := hAB.const_mul p
    simpa using this
  have hd := hfin.deriv
  rw [show (fun t : ℝ => p * sq (x + t • axis i) ^ (p - 1) * (2 * x i + 2 * t))
      = fun t => p * (sq (x + t • axis i) ^ (p - 1) * (2 * x i + 2 * t)) from by
    funext t; ring]
  rw [hd]
  have hsub : p - 1 - 1 = p - 2 := by ring
  rw [hsub]
  ring

end Radial


/-- **The Laplacian of `(sq ·)^p`**, in Maxwell's sign: the partial derivatives of
`y ↦ (sq y)^p` at a point where `sq ≠ 0`. -/
theorem maxwellNabla2_sq_rpow (p : ℝ) {x : Vec3} (hx : 0 < sq x) :
    maxwellNabla2 (fun y => (sq y) ^ p) x = -(4 * p ^ 2 + 2 * p) * (sq x) ^ (p - 1) := by
  have hSp : (sq x) ^ (p - 2) * sq x = (sq x) ^ (p - 1) := by
    have h1 : (sq x) ^ (p - 2) * (sq x) ^ (1 : ℝ) = (sq x) ^ (p - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    simpa using h1
  have hsum : (∑ i : Fin 3, pd i (fun y => pd i (fun z => (sq z) ^ p) y) x)
      = 4 * (p * (p - 1)) * ((sq x) ^ (p - 2) * sq x) + 6 * (p * (sq x) ^ (p - 1)) := by
    simp only [pd_pd_sq_rpow p hx, Fin.sum_univ_three]
    have hsq : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = sq x := (sq_eq x).symm
    linear_combination (4 * (p * (p - 1)) * (sq x) ^ (p - 2)) * hsq
  simp only [maxwellNabla2, hsum, hSp]
  ring


/-! ## Congruence lemmas -/

section Congr

theorem pd_congr {f g : Vec3 → ℝ} {x : Vec3} (h : f =ᶠ[𝓝 x] g) (i : Fin 3) :
    pd i f x = pd i g x := by
  unfold pd
  rw [h.fderiv_eq]

theorem eventually_eventuallyEq {f g : Vec3 → ℝ} {x : Vec3} (h : f =ᶠ[𝓝 x] g) :
    ∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g := by
  simp only [Filter.EventuallyEq] at h ⊢
  rw [eventually_nhds_iff] at h ⊢
  obtain ⟨t, hpt, htop, hmem⟩ := h
  exact ⟨t, fun y hy => eventually_nhds_iff.mpr ⟨t, hpt, htop, hy⟩, htop, hmem⟩

theorem maxwellNabla2_congr {f g : Vec3 → ℝ} {x : Vec3} (h : f =ᶠ[𝓝 x] g) :
    maxwellNabla2 f x = maxwellNabla2 g x := by
  have h2 := eventually_eventuallyEq h
  unfold maxwellNabla2
  congr 1
  exact Finset.sum_congr rfl fun i _ => pd_congr (h2.mono fun y hy => pd_congr hy i) i

end Congr

/-! ## The Newtonian kernel is harmonic off the source -/

section Kernel

/-- `1/‖x‖ = (x·x)^{-1/2}`: the two forms of the singular kernel. -/
theorem inv_eNorm_eq_rpow {x : Vec3} (hx : x ≠ 0) :
    1 / eNorm x = (sq x) ^ (-(1 / 2) : ℝ) := by
  have h0 : (0 : ℝ) ≤ sq x := sq_nonneg' x
  have h : (sq x) ^ (-(1 / 2) : ℝ) = ((sq x) ^ ((1 / 2) : ℝ))⁻¹ := Real.rpow_neg h0 (1 / 2)
  rw [h, eNorm, Real.sqrt_eq_rpow]
  exact one_div _

theorem contDiffAt_inv_eNorm {z : Vec3} (hz : z ≠ 0) :
    ContDiffAt ℝ 2 (fun y : Vec3 => 1 / eNorm y) z := by
  have hsp : 0 < sq z := sq_pos_iff.mpr hz
  have hsq : ContDiffAt ℝ 2 (fun y : Vec3 => sq y) z := by
    have h : sq = fun y : Vec3 => y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      funext y; rw [sq_eq]
    rw [h]; fun_prop
  have hrpow : ContDiffAt ℝ 2 (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) (sq z) :=
    Real.contDiffAt_rpow_const (n := 2) (Or.inl (ne_of_gt hsp))
  have h2 := hrpow.comp z hsq
  have heq : (fun y : Vec3 => 1 / eNorm y) =ᶠ[𝓝 z]
      fun y => (sq y) ^ (-(1 / 2) : ℝ) := by
    filter_upwards [eventually_ne_nhds hz] with y hy
    exact inv_eNorm_eq_rpow hy
  exact h2.congr_of_eventuallyEq (by simpa [Function.comp_def] using heq)

/-- **The Newtonian kernel `1/r` is Maxwell-harmonic in `x` off the source**: `∇²(1/r) = 0`. -/
theorem maxwellNabla2_inv_eNorm {z : Vec3} (hz : z ≠ 0) :
    maxwellNabla2 (fun y : Vec3 => 1 / eNorm y) z = 0 := by
  have hsp : 0 < sq z := sq_pos_iff.mpr hz
  have hgen : maxwellNabla2 (fun y : Vec3 => (sq y) ^ (-(1 / 2) : ℝ)) z = 0 := by
    have h := maxwellNabla2_sq_rpow (-(1 / 2) : ℝ) hsp
    have hcoef : (4 * (-(1 / 2) : ℝ) ^ 2 + 2 * (-(1 / 2))) = 0 := by norm_num
    rw [hcoef] at h
    simpa using h
  rw [maxwellNabla2_congr (f := fun y : Vec3 => 1 / eNorm y)
    (g := fun y => (sq y) ^ (-(1 / 2) : ℝ)) ?_]
  exact hgen
  filter_upwards [eventually_ne_nhds hz] with y hy
  exact inv_eNorm_eq_rpow hy

/-- Translation: `pd` and `maxwellNabla2` only see the shape of the function. -/
theorem pd_sub_const {f : Vec3 → ℝ} {x s : Vec3} (i : Fin 3)
    (hf : DifferentiableAt ℝ f (x - s)) :
    pd i (fun y => f (y - s)) x = pd i f (x - s) := by
  have hcomp : DifferentiableAt ℝ (fun y : Vec3 => f (y - s)) x :=
    hf.comp x ((differentiableAt_id (x := x)).sub (differentiableAt_const (c := s)))
  rw [pd_eq_deriv_line i hcomp, pd_eq_deriv_line i hf]
  congr 1
  funext t
  congr 1
  abel

theorem pd_pd_sub_const {f : Vec3 → ℝ} {x s : Vec3} (i : Fin 3)
    (hf : ContDiffAt ℝ 2 f (x - s)) :
    pd i (fun y => pd i (fun z => f (z - s)) y) x = pd i (fun z => pd i f z) (x - s) := by
  have hC : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f (y - s) := by
    have h1 : ∀ᶠ z in 𝓝 (x - s), ContDiffAt ℝ 2 f z := hf.eventually (by simp)
    have htend : Tendsto (fun y : Vec3 => y - s) (𝓝 x) (𝓝 (x - s)) :=
      (continuous_id.sub continuous_const).tendsto x
    exact htend.eventually h1
  have heq : (fun y => pd i (fun z => f (z - s)) y) =ᶠ[𝓝 x] (fun y => pd i f (y - s)) := by
    filter_upwards [hC] with y hy
    exact pd_sub_const i (hy.differentiableAt (by norm_num))
  rw [pd_congr heq i, pd_sub_const i (differentiableAt_pd hf i)]

theorem maxwellNabla2_sub_const {f : Vec3 → ℝ} {x s : Vec3} (hf : ContDiffAt ℝ 2 f (x - s)) :
    maxwellNabla2 (fun y => f (y - s)) x = maxwellNabla2 f (x - s) := by
  unfold maxwellNabla2
  congr 1
  exact Finset.sum_congr rfl fun i _ => pd_pd_sub_const i hf

/-- **Art. 616–618, the singular kernel:** the potential `1/‖x − y‖` of a unit source at `y` is
Maxwell-harmonic in `x` at every point off the source. -/
theorem maxwellNabla2_newtonKernel {s x : Vec3} (h : x ≠ s) :
    maxwellNabla2 (fun y => newtonKernel s y) x = 0 := by
  have hxs : x - s ≠ 0 := sub_ne_zero.mpr h
  have hC : ContDiffAt ℝ 2 (fun z : Vec3 => 1 / eNorm z) (x - s) := contDiffAt_inv_eNorm hxs
  rw [show (fun y => newtonKernel s y) = fun y => (fun z : Vec3 => 1 / eNorm z) (y - s) from rfl,
    maxwellNabla2_sub_const hC, maxwellNabla2_inv_eNorm hxs]

end Kernel


/-! ## The Newtonian potential of a compactly supported source: decay at infinity -/

section Potential

/-- The Newtonian potential of the component `i` of a source `C`: Maxwell's `∭ C/r`, with
Euclidean `r`. -/
noncomputable def newtonPotential (C : Vec3 → Vec3) (i : Fin 3) (x : Vec3) : ℝ :=
  ∫ y, C y i * newtonKernel y x

theorem infDist_pos_of_notMem {K : Set Vec3} (hK : IsCompact K) (hne : K.Nonempty)
    {x : Vec3} (hx : x ∉ K) : 0 < Metric.infDist x K :=
  (hK.isClosed.notMem_iff_infDist_pos hne).mp hx

/-- **Art. 617, "vanishes at an infinite distance".** The Newtonian potential of a continuous
compactly supported source tends to `0` at infinity. -/
theorem newtonPotential_tendsto_zero {C : Vec3 → Vec3} (hC : Continuous C)
    (hsC : HasCompactSupport C) (i : Fin 3) :
    Tendsto (newtonPotential C i) (cocompact Vec3) (𝓝 0) := by
  classical
  set K := tsupport C with hKdef
  have hKc : IsCompact K := hsC.isCompact
  rcases Set.eq_empty_or_nonempty K with hE | hne
  · -- a source with empty support is identically zero
    have hCsupp : C = 0 := by
      funext y
      have hy : y ∉ tsupport C := by rw [← hKdef, hE]; exact Set.notMem_empty y
      exact image_eq_zero_of_notMem_tsupport hy
    have hzero : newtonPotential C i = fun _ => 0 := by
      funext x
      simp [newtonPotential, hCsupp]
    rw [hzero]
    exact tendsto_const_nhds
  obtain ⟨k₀, hk₀⟩ := hne
  obtain ⟨M, hM⟩ := hC.bounded_above_of_compact_support hsC
  have hMi : ∀ y : Vec3, |C y i| ≤ M := by
    intro y
    have h1 : |C y i| ≤ ‖C y‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (C y) i
    exact h1.trans (hM y)
  -- the pointwise bound on the complement of the support
  have hbound : ∀ x : Vec3, x ∉ K →
      ‖newtonPotential C i x‖ ≤ M * volume.real K / Metric.infDist x K := by
    intro x hx
    have hρ : 0 < Metric.infDist x K := infDist_pos_of_notMem hKc ⟨k₀, hk₀⟩ hx
    have hρne : Metric.infDist x K ≠ 0 := ne_of_gt hρ
    have hzero : ∀ y ∉ K, C y i * newtonKernel y x = 0 := by
      intro y hy
      simp only [newtonKernel, image_eq_zero_of_notMem_tsupport hy, Pi.zero_apply, zero_mul]
    rw [newtonPotential, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hpt : ∀ y ∈ K, ‖C y i * newtonKernel y x‖ ≤ M / Metric.infDist x K := by
      intro y hy
      have hdist : Metric.infDist x K ≤ dist x y := Metric.infDist_le_dist_of_mem hy
      have hnorm : dist x y ≤ eNorm (x - y) := by
        rw [dist_eq_norm]; exact norm_le_eNorm _
      have hpos : 0 < eNorm (x - y) := lt_of_lt_of_le hρ (le_trans hdist hnorm)
      have hKY : newtonKernel y x = 1 / eNorm (x - y) := rfl
      rw [hKY, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / eNorm (x - y))]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul (hMi y) ?_ (by positivity) (le_trans (abs_nonneg _) (hMi y))
      simpa [one_div] using one_div_le_one_div_of_le hρ (le_trans hdist hnorm)
    calc ‖∫ y in K, C y i * newtonKernel y x‖
        ≤ (M / Metric.infDist x K) * volume.real K :=
          norm_setIntegral_le_of_norm_le_const hKc.measure_lt_top hpt
      _ = M * volume.real K / Metric.infDist x K := by ring
  -- the reciprocal of the distance to a compact set tends to `0` at infinity
  have hρtend : Tendsto (fun x : Vec3 => Metric.infDist x K) (cocompact Vec3) atTop := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec3)).1 hKc.isBounded
    have hD : ∀ k ∈ K, dist k₀ k ≤ dist k₀ 0 + R := by
      intro k hk
      have h1 : dist k 0 ≤ R := by
        simpa [dist_eq_norm, dist_comm] using hR hk
      calc dist k₀ k ≤ dist k₀ 0 + dist 0 k := dist_triangle _ _ _
        _ = dist k₀ 0 + dist k 0 := by rw [dist_comm (0 : Vec3) k]
        _ ≤ dist k₀ 0 + R := by linarith
    have hle : ∀ x : Vec3, ∀ k ∈ K, dist x k₀ - (dist k₀ 0 + R) ≤ dist x k := by
      intro x k hk
      have h2 := hD k hk
      have h3 : dist x k₀ ≤ dist x k + dist k k₀ := dist_triangle _ _ _
      rw [dist_comm k k₀] at h3
      linarith
    have hmono : ∀ x : Vec3, dist x k₀ - (dist k₀ 0 + R) ≤ Metric.infDist x K :=
      fun x => (Metric.le_infDist ⟨k₀, hk₀⟩).mpr (fun k hk => hle x k hk)
    have h1 : Tendsto (fun x : Vec3 => dist x k₀ - (dist k₀ 0 + R)) (cocompact Vec3) atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right _ _ (tendsto_dist_right_cocompact_atTop k₀)
    exact tendsto_atTop_mono' _ (Eventually.of_forall hmono) h1
  have hlim : Tendsto (fun x : Vec3 => M * volume.real K / Metric.infDist x K)
      (cocompact Vec3) (𝓝 0) := hρtend.const_div_atTop (M * volume.real K)
  refine squeeze_zero_norm' ?_ hlim
  have hKc' : Kᶜ ∈ cocompact Vec3 := hKc.compl_mem_cocompact
  filter_upwards [hKc'] with x hx
  exact hbound x hx

end Potential


/-! ## Linearity, and the exact reduction of Art. 617 existence to the singular integral -/

section Reduction

theorem maxwellNabla2_const_mul (c : ℝ) {f : Vec3 → ℝ} {x : Vec3} (hf : ContDiff ℝ 2 f) :
    maxwellNabla2 (fun y => c * f y) x = c * maxwellNabla2 f x := by
  have e : ∀ i : Fin 3, (fun y => pd i (fun z => c * f z) y) = fun y => c * pd i f y := by
    intro i
    funext y
    exact pd_const_mul i c (hf.differentiable (by norm_num) y)
  simp only [maxwellNabla2, e, pd_const_mul _ c (differentiableAt_pd hf.contDiffAt _)]
  rw [← Finset.mul_sum]
  ring

theorem div_const_mul (c : ℝ) {F : Vec3 → Vec3} {x : Vec3}
    (hF : ∀ i, DifferentiableAt ℝ (fun y => F y i) x) :
    div (fun y => c • F y) x = c * div F x := by
  simp only [div, Pi.smul_apply, smul_eq_mul, pd_const_mul _ c (hF _), Finset.mul_sum]

/-- **The singular-integral content of Art. 616–617.** For a smooth source `C` with compact
support, the Newtonian potential `x ↦ ∫ y, C y i / ‖x − y‖` is `C²` and satisfies Maxwell's
Poisson equation `∇²𝔄 = 4πC` componentwise. What is missing in Mathlib is exactly this:
(i) second-order differentiation under the singular integral (the integrand `1/‖x−y‖` is not
integrable in `C²`-norm on a neighbourhood of the diagonal — one needs the standard "subtract
the local mean" trick of Evans, *PDE* §2.2.1, or the truncated-kernel limit), and (ii) the
solid-angle/sphere-surface computation `∮_{‖x−y‖=ε} ∂_ν(1/‖x−y‖) dS → −4π`. -/
def NewtonianPotentialSolvesPoisson : Prop :=
  ∀ (C : Vec3 → Vec3) (i : Fin 3), ContDiff ℝ ⊤ C → HasCompactSupport C →
    ContDiff ℝ 2 (newtonPotential C i) ∧
      ∀ x, maxwellNabla2 (newtonPotential C i) x = fourPi * C x i

/-- The first-order part of the same singular integral: for a solenoidal source `div C = 0` the
potential is solenoidal, `div (∫ y, C y/‖x−y‖) = 0`. This is the gauge condition `S.∇𝔄 = 0` of
Art. 617 for the potential; it needs `∫ |C y|/‖x−y‖² dy < ∞`, i.e. the local integrability of
`r⁻²` in `ℝ³` (true: `∫_{‖z‖<1} ‖z‖^{-2} dz = 4π`). -/
def NewtonianPotentialIsSolenoidal : Prop :=
  ∀ C : Vec3 → Vec3, ContDiff ℝ ⊤ C → HasCompactSupport C → (∀ x, div C x = 0) →
    ∀ x, div (fun z i => newtonPotential C i z) x = 0

/-- **Art. 617, the existence half, reduced to the singular integral.** Assuming the two named
singular-integral statements above, Maxwell's potential `𝔄 x i = μ ∫ y, C y i/‖x − y‖` is `C²`,
solenoidal, satisfies `∇²𝔄 = 4πμC`, and vanishes at infinity (the last **proved here**,
`newtonPotential_tendsto_zero`, from the compact support alone). -/
theorem art617_existence_of_poisson (hP : NewtonianPotentialSolvesPoisson)
    (hS : NewtonianPotentialIsSolenoidal) :
    ∀ (μ : ℝ) (C : Vec3 → Vec3), ContDiff ℝ ⊤ C → HasCompactSupport C → (∀ x, div C x = 0) →
      ∃ A : Vec3 → Vec3, ContDiff ℝ 2 A ∧ (∀ x, div A x = 0) ∧
        (∀ i x, maxwellNabla2 (fun y => A y i) x = fourPi * μ * C x i) ∧
        Tendsto A (cocompact Vec3) (𝓝 0) := by
  intro μ C hC hsC hdiv
  have hC2 : ∀ i, ContDiff ℝ 2 (newtonPotential C i) := fun i => (hP C i hC hsC).1
  have hPoisson : ∀ i x, maxwellNabla2 (newtonPotential C i) x = fourPi * C x i :=
    fun i => (hP C i hC hsC).2
  have hdecay : ∀ i, Tendsto (fun x => μ * newtonPotential C i x) (cocompact Vec3) (𝓝 0) := by
    intro i
    have h := (newtonPotential_tendsto_zero hC.continuous hsC i).const_mul μ
    simpa using h
  refine ⟨fun x i => μ * newtonPotential C i x, ?_, ?_, ?_, ?_⟩
  · exact contDiff_pi.2 fun i => contDiff_const.mul (hC2 i)
  · intro x
    have h1 : (fun y => (fun x i => μ * newtonPotential C i x) y) = fun y => μ • fun i =>
        newtonPotential C i y := rfl
    rw [h1, div_const_mul μ (fun i => ?_)]
    · rw [hS C hC hsC hdiv, mul_zero]
    · exact ((hC2 i).differentiable (by norm_num) x)
  · intro i x
    have h1 : (fun y => (fun x i => μ * newtonPotential C i x) y i)
        = fun y => μ * newtonPotential C i y := rfl
    rw [h1, maxwellNabla2_const_mul μ (hC2 i), hPoisson i x]
    ring
  · exact tendsto_pi_nhds.mpr hdecay

end Reduction

end Maxwell
