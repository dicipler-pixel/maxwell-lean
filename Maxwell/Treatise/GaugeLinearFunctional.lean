/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.VectorPotential
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Art. 616: solving Maxwell's `∇²χ = J` for one-dimensional profiles

`Maxwell.Statements.Art616GaugeChoiceAvailable` asks whether every smooth compactly supported
`𝔄` admits a `C²` `χ` with `div (𝔄 + ∇χ) = 0`. By `art616_gauge_iff_poisson` this is exactly
Maxwell's Poisson equation `∇²χ = div 𝔄` (his sign, `∇² = −Δ`).

This file *solves* that equation in closed form for a class of sources: whenever
`J x = ∑_k g_k (x ⬝ᵥ w_k)` is a finite sum of functions of one linear functional (`w_k ≠ 0`),

  `χ x = −∑_k G_k (x ⬝ᵥ w_k) / (w_k ⬝ᵥ w_k)`,   where `G_k'' = g_k`,

is `C²` and satisfies `maxwellNabla2 χ x = J x` at every `x`. Hence the gauge can be chosen
(`exists_gauge_of_finset_dotProduct`), with no existence theorem for Poisson's equation assumed.

The content is the chain rule for `x ↦ G (x ⬝ᵥ w)` plus `∑_i w_i w_i = w ⬝ᵥ w`; no analysis
beyond derivatives of compositions with a continuous linear functional is used.

What is *not* done: the general statement needs `∇²χ = J` for arbitrary smooth compactly
supported `J`, i.e. the Newtonian potential of Art. 616 eqs. (5)–(7). That is isolated as
`NewtonianPotentialSolver` and shown to imply `Art616GaugeChoiceAvailable`
(`art616GaugeChoiceAvailable_of_poissonSolver`).
-/

namespace Maxwell
open Matrix
open Filter
open scoped Topology

/-! ## The linear functional `x ↦ x ⬝ᵥ w` -/

/-- `x ↦ x ⬝ᵥ w` as a continuous linear map. -/
noncomputable def dotCLM (w : Vec3) : Vec3 →L[ℝ] ℝ :=
  ∑ i, w i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i

theorem dotCLM_apply (w v : Vec3) : dotCLM w v = v ⬝ᵥ w := by
  simp only [dotCLM, _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, dotProduct, mul_comm]

theorem dotCLM_axis (w : Vec3) (i : Fin 3) : dotCLM w (axis i) = w i := by
  rw [dotCLM_apply]
  simp [axis, dotProduct, Pi.single_apply]

/-- `w ⬝ᵥ w > 0` for `w ≠ 0`. -/
theorem dotProduct_self_pos {w : Vec3} (hw : w ≠ 0) : 0 < w ⬝ᵥ w := by
  have h1 : w ⬝ᵥ w = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := sq_eq w
  have h2 : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext fun i => by fin_cases i <;> simp_all)
  rw [h1]
  rcases h2 with h | h | h
  · nlinarith [(mul_self_pos).mpr h, sq_nonneg (w 1), sq_nonneg (w 2)]
  · nlinarith [(mul_self_pos).mpr h, sq_nonneg (w 0), sq_nonneg (w 2)]
  · nlinarith [(mul_self_pos).mpr h, sq_nonneg (w 0), sq_nonneg (w 1)]

/-! ## Chain rule for a function of one linear functional -/

theorem hasFDerivAt_comp_dotCLM {G G' : ℝ → ℝ} (hG : ∀ t, HasDerivAt G (G' t) t) (w x : Vec3) :
    HasFDerivAt (fun y => G (y ⬝ᵥ w))
      (ContinuousLinearMap.toSpanSingleton ℝ (G' (x ⬝ᵥ w)) ∘SL dotCLM w) x := by
  have h := (hG (dotCLM w x)).hasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt (dotCLM w))
  simpa only [dotCLM_apply, Function.comp_def] using h

theorem differentiableAt_comp_dotCLM {G G' : ℝ → ℝ} (hG : ∀ t, HasDerivAt G (G' t) t)
    (w x : Vec3) : DifferentiableAt ℝ (fun y => G (y ⬝ᵥ w)) x :=
  (hasFDerivAt_comp_dotCLM hG w x).differentiableAt

/-- `∂_i (G (x ⬝ᵥ w)) = G' (x ⬝ᵥ w) * w_i`. -/
theorem pd_comp_dotCLM {G G' : ℝ → ℝ} (hG : ∀ t, HasDerivAt G (G' t) t) (w x : Vec3)
    (i : Fin 3) : pd i (fun y => G (y ⬝ᵥ w)) x = G' (x ⬝ᵥ w) * w i := by
  have h := (hasFDerivAt_comp_dotCLM hG w x).fderiv
  rw [pd, h]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, dotCLM_axis]
  ring

/-! ## `C²` of a function with a second antiderivative -/

theorem contDiff_two_of_hasDerivAt {G G1 g : ℝ → ℝ}
    (hG : ∀ t, HasDerivAt G (G1 t) t) (hG1 : ∀ t, HasDerivAt G1 (g t) t)
    (hg : Continuous g) : ContDiff ℝ 2 G := by
  have hderivG : deriv G = G1 := funext fun t => (hG t).deriv
  have hderivG1 : deriv G1 = g := funext fun t => (hG1 t).deriv
  have h1 : ContDiff ℝ 1 G1 := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun t => (hG1 t).differentiableAt, by rw [hderivG1]; exact hg⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from by norm_num, contDiff_succ_iff_deriv]
  exact ⟨fun t => (hG t).differentiableAt, by simp, by rwa [hderivG]⟩

/-! ## The gauge potential `χ = −G (x ⬝ᵥ w) / (w ⬝ᵥ w)` -/

/-- Maxwell's `χ` for a source `g (x ⬝ᵥ w)`, written with a second antiderivative `G` of `g`. -/
noncomputable def gaugeChi (G : ℝ → ℝ) (w : Vec3) : Vec3 → ℝ :=
  fun x => - G (x ⬝ᵥ w) / (w ⬝ᵥ w)

theorem contDiff_gaugeChi {G G1 g : ℝ → ℝ} (hG : ∀ t, HasDerivAt G (G1 t) t)
    (hG1 : ∀ t, HasDerivAt G1 (g t) t) (hg : Continuous g) (w : Vec3) :
    ContDiff ℝ 2 (gaugeChi G w) := by
  have hGc : ContDiff ℝ 2 G := contDiff_two_of_hasDerivAt hG hG1 hg
  have hcomp : ContDiff ℝ 2 (fun x : Vec3 => G (dotCLM w x)) :=
    hGc.comp (ContinuousLinearMap.contDiff (dotCLM w))
  have h2 : ContDiff ℝ 2 (fun x : Vec3 => G (x ⬝ᵥ w)) := by
    simpa only [dotCLM_apply] using hcomp
  exact h2.neg.div_const (w ⬝ᵥ w)

theorem pd_gaugeChi {G G1 : ℝ → ℝ} (hG : ∀ t, HasDerivAt G (G1 t) t) (w x : Vec3) (i : Fin 3) :
    pd i (gaugeChi G w) x = - (G1 (x ⬝ᵥ w) * w i) / (w ⬝ᵥ w) := by
  have hfun : gaugeChi G w = fun y => (-(w ⬝ᵥ w))⁻¹ * G (y ⬝ᵥ w) := by
    funext y
    simp [gaugeChi, div_eq_mul_inv]
    ring
  rw [hfun, pd_const_mul _ _ (differentiableAt_comp_dotCLM hG w x), pd_comp_dotCLM hG w x]
  ring

theorem pd_pd_gaugeChi {G G1 g : ℝ → ℝ} (hG : ∀ t, HasDerivAt G (G1 t) t)
    (hG1 : ∀ t, HasDerivAt G1 (g t) t) (w x : Vec3) (i : Fin 3) :
    pd i (fun y => pd i (gaugeChi G w) y) x = - (g (x ⬝ᵥ w) * w i * w i) / (w ⬝ᵥ w) := by
  have hfun : (fun y => pd i (gaugeChi G w) y) =
      fun y => (-(w ⬝ᵥ w))⁻¹ * w i * G1 (y ⬝ᵥ w) := by
    funext y
    rw [pd_gaugeChi hG w y i]
    simp only [div_eq_mul_inv]
    ring
  rw [hfun, pd_const_mul _ _ (differentiableAt_comp_dotCLM hG1 w x), pd_comp_dotCLM hG1 w x]
  ring

/-- **Maxwell's Poisson equation `∇²χ = g (x ⬝ᵥ w)`** (his sign: `∇² = −Δ`), solved in closed
form by `χ = −G (x ⬝ᵥ w)/(w ⬝ᵥ w)` with `G'' = g`. -/
theorem maxwellNabla2_gaugeChi {G G1 g : ℝ → ℝ} (hG : ∀ t, HasDerivAt G (G1 t) t)
    (hG1 : ∀ t, HasDerivAt G1 (g t) t) {w : Vec3} (hw : w ≠ 0) (x : Vec3) :
    maxwellNabla2 (gaugeChi G w) x = g (x ⬝ᵥ w) := by
  have hc : w ⬝ᵥ w ≠ 0 := ne_of_gt (dotProduct_self_pos hw)
  have hsum : ∑ i : Fin 3, w i * w i = w ⬝ᵥ w := by
    simp [dotProduct]
  simp only [maxwellNabla2, pd_pd_gaugeChi hG hG1 w x]
  have hterm : ∀ i : Fin 3, - (g (x ⬝ᵥ w) * w i * w i) / (w ⬝ᵥ w)
      = (-(g (x ⬝ᵥ w)) / (w ⬝ᵥ w)) * (w i * w i) := by
    intro i
    field_simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, hsum]
  field_simp

/-- **Poisson's equation solved for a profile source**: `∇²χ = g (x ⬝ᵥ w)`, in the exact form of
the conclusion of `NewtonianPotentialSolver` (but for a non-compactly-supported, profile `J`). -/
theorem poisson_profile {g G1 G : ℝ → ℝ} {w : Vec3} (hw : w ≠ 0)
    (hG : ∀ t, HasDerivAt G (G1 t) t) (hG1 : ∀ t, HasDerivAt G1 (g t) t)
    (hg : Continuous g) :
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, maxwellNabla2 χ x = g (x ⬝ᵥ w) :=
  ⟨gaugeChi G w, contDiff_gaugeChi hG hG1 hg w, fun x => maxwellNabla2_gaugeChi hG hG1 hw x⟩

/-! ## Finite sums of profiles: linearity of `∇²` -/

theorem differentiableAt_finset_sum {ι : Type} (s : Finset ι) (f : ι → Vec3 → ℝ) (x : Vec3)
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) x) :
    DifferentiableAt ℝ (fun y => ∑ k ∈ s, f k y) x := by
  simpa only [Finset.sum_fn] using DifferentiableAt.sum (u := s) (A := f) (fun k hk => hf k hk)

theorem pd_finset_sum {ι : Type} (s : Finset ι) (f : ι → Vec3 → ℝ) (x : Vec3) (i : Fin 3)
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) x) :
    pd i (fun y => ∑ k ∈ s, f k y) x = ∑ k ∈ s, pd i (f k) x := by
  have hd : fderiv ℝ (fun y => ∑ k ∈ s, f k y) x = ∑ k ∈ s, fderiv ℝ (f k) x := by
    simpa only [Finset.sum_fn] using fderiv_sum (u := s) (A := f) (x := x) (fun k hk => hf k hk)
  rw [pd, hd, _root_.sum_apply]
  rfl

theorem maxwellNabla2_finset_sum {ι : Type} (s : Finset ι) (f : ι → Vec3 → ℝ) (x : Vec3)
    (hf : ∀ k ∈ s, ContDiff ℝ 2 (f k)) :
    maxwellNabla2 (fun y => ∑ k ∈ s, f k y) x = ∑ k ∈ s, maxwellNabla2 (f k) x := by
  have h1 : ∀ i : Fin 3,
      (fun y => pd i (fun z => ∑ k ∈ s, f k z) y) = fun y => ∑ k ∈ s, pd i (f k) y := by
    intro i
    funext y
    exact pd_finset_sum s f y i (fun k hk => (hf k hk).differentiable (by norm_num) y)
  have h2 : ∀ i : Fin 3,
      pd i (fun y => ∑ k ∈ s, pd i (f k) y) x = ∑ k ∈ s, pd i (fun y => pd i (f k) y) x := by
    intro i
    exact pd_finset_sum s (fun k y => pd i (f k) y) x i
      (fun k hk => differentiableAt_pd (hf k hk).contDiffAt i)
  simp only [maxwellNabla2, h1, h2]
  rw [Finset.sum_comm]
  simp [Finset.sum_neg_distrib]

/-! ## The gauge exists when `div 𝔄` is a finite sum of profiles -/

/-- **Art. 616, gauge available for profile sources.** If the divergence of `𝔄` is a finite sum
`∑_k g_k (x ⬝ᵥ w_k)` with `w_k ≠ 0`, then `χ = −∑_k G_k (x ⬝ᵥ w_k)/(w_k ⬝ᵥ w_k)` (with
`G_k'' = g_k`) is `C²` and makes `𝔄 + ∇χ` solenoidal. -/
theorem exists_gauge_of_finset_dotProduct {ι : Type} (s : Finset ι)
    (g G1 G : ι → ℝ → ℝ) (w : ι → Vec3) {A : Vec3 → Vec3}
    (hw : ∀ k ∈ s, w k ≠ 0)
    (hdiv : ∀ x, div A x = ∑ k ∈ s, g k (x ⬝ᵥ w k))
    (hA : ∀ i, Differentiable ℝ (fun y => A y i))
    (hG : ∀ k ∈ s, ∀ t, HasDerivAt (G k) (G1 k t) t)
    (hG1 : ∀ k ∈ s, ∀ t, HasDerivAt (G1 k) (g k t) t)
    (hg : ∀ k ∈ s, Continuous (g k)) :
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, div (fun y => A y + grad χ y) x = 0 := by
  classical
  refine ⟨fun x => ∑ k ∈ s, gaugeChi (G k) (w k) x, ?_, ?_⟩
  · exact ContDiff.sum (fun k hk => contDiff_gaugeChi (hG k hk) (hG1 k hk) (hg k hk) (w k))
  · intro x
    have hχ : ContDiffAt ℝ 2 (fun x => ∑ k ∈ s, gaugeChi (G k) (w k) x) x :=
      (ContDiff.sum (fun k hk =>
        contDiff_gaugeChi (hG k hk) (hG1 k hk) (hg k hk) (w k))).contDiffAt
    rw [div_add_grad (fun i => hA i x) hχ,
      maxwellNabla2_finset_sum s (fun k y => gaugeChi (G k) (w k) y) x
        (fun k hk => contDiff_gaugeChi (hG k hk) (hG1 k hk) (hg k hk) (w k)),
      Finset.sum_congr rfl (fun k hk => maxwellNabla2_gaugeChi (hG k hk) (hG1 k hk)
        (hw k hk) x), hdiv]
    simp

/-- **Poisson's equation solved for a finite sum of profiles**: `∇²χ = ∑_k g_k (x ⬝ᵥ w_k)`. -/
theorem poisson_finset_profile {ι : Type} (s : Finset ι) (g G1 G : ι → ℝ → ℝ)
    (w : ι → Vec3) (hw : ∀ k ∈ s, w k ≠ 0)
    (hG : ∀ k ∈ s, ∀ t, HasDerivAt (G k) (G1 k t) t)
    (hG1 : ∀ k ∈ s, ∀ t, HasDerivAt (G1 k) (g k t) t)
    (hg : ∀ k ∈ s, Continuous (g k)) :
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧
      ∀ x, maxwellNabla2 χ x = ∑ k ∈ s, g k (x ⬝ᵥ w k) := by
  refine ⟨fun x => ∑ k ∈ s, gaugeChi (G k) (w k) x,
    ContDiff.sum (fun k hk => contDiff_gaugeChi (hG k hk) (hG1 k hk) (hg k hk) (w k)), ?_⟩
  intro x
  rw [maxwellNabla2_finset_sum s (fun k y => gaugeChi (G k) (w k) y) x
      (fun k hk => contDiff_gaugeChi (hG k hk) (hG1 k hk) (hg k hk) (w k)),
    Finset.sum_congr rfl (fun k hk => maxwellNabla2_gaugeChi (hG k hk) (hG1 k hk) (hw k hk) x)]

/-- Single-profile form. -/
theorem exists_gauge_of_dotProduct {g G1 G : ℝ → ℝ} {w : Vec3} {A : Vec3 → Vec3}
    (hw : w ≠ 0) (hdiv : ∀ x, div A x = g (x ⬝ᵥ w))
    (hA : ∀ i, Differentiable ℝ (fun y => A y i))
    (hG : ∀ t, HasDerivAt G (G1 t) t) (hG1 : ∀ t, HasDerivAt G1 (g t) t)
    (hg : Continuous g) :
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, div (fun y => A y + grad χ y) x = 0 := by
  obtain ⟨χ, hχ, h⟩ := exists_gauge_of_finset_dotProduct {0} (fun _ => g) (fun _ => G1)
    (fun _ => G) (fun _ => w) (fun k _ => hw)
    (fun x => by simpa using hdiv x) hA (fun k _ => hG) (fun k _ => hG1) (fun k _ => hg)
  exact ⟨χ, hχ, h⟩

/-! ## The general statement reduces to solving Poisson's equation -/

/-- **The exact missing lemma for `Art616GaugeChoiceAvailable`**: Poisson's equation `∇²χ = J`
(Maxwell's sign) is solvable for every smooth compactly supported `J`. This is what Art. 616
eqs. (5)–(7) build with the Newtonian potential `χ = (1/4π)∭ J/r`; nothing in this file proves
it, and the file above solves the equation only for profile sources `∑_k g_k (x ⬝ᵥ w_k)`. -/
def NewtonianPotentialSolver : Prop :=
  ∀ J : Vec3 → ℝ, ContDiff ℝ ⊤ J → HasCompactSupport J →
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧ ∀ x, maxwellNabla2 χ x = J x

theorem contDiff_pd {f : Vec3 → ℝ} (h : ContDiff ℝ ⊤ f) (i : Fin 3) :
    ContDiff ℝ ⊤ (fun x => pd i f x) := by
  have h2 : ContDiff ℝ ⊤ (fderiv ℝ f) := h.fderiv_right (m := ⊤) le_rfl
  have key := h2.clm_apply (contDiff_const (c := axis i))
  simpa only [pd] using key

theorem hasCompactSupport_apply {A : Vec3 → Vec3} (hA : HasCompactSupport A) (i : Fin 3) :
    HasCompactSupport (fun y => A y i) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hA ⊢
  filter_upwards [hA] with y hy
  simp [hy]

theorem hasCompactSupport_pd {f : Vec3 → ℝ} (h : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (fun x => pd i f x) := by
  have h2 : HasCompactSupport (fderiv ℝ f) := HasCompactSupport.fderiv ℝ h
  rw [hasCompactSupport_iff_eventuallyEq] at h2 ⊢
  filter_upwards [h2] with x hx
  simp [pd, hx]

theorem contDiff_div {A : Vec3 → Vec3} (hA : ContDiff ℝ ⊤ A) : ContDiff ℝ ⊤ (div A) := by
  have hpd : ∀ i : Fin 3, ContDiff ℝ ⊤ (fun x => pd i (fun y => A y i) x) := by
    intro i
    have h1 : ContDiff ℝ ⊤ (fun y => A y i) := contDiff_pi.1 hA i
    have h2 : ContDiff ℝ ⊤ (fderiv ℝ (fun y => A y i)) := h1.fderiv_right (m := ⊤) le_rfl
    have key := h2.clm_apply (contDiff_const (c := axis i))
    simpa only [pd] using key
  have hsum := ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i x => pd i (fun y => A y i) x) (fun i _ => hpd i)
  have hgoal : div A = fun x => ∑ i : Fin 3, pd i (fun y => A y i) x := rfl
  rw [hgoal, ← Finset.sum_fn]
  exact hsum

theorem hasCompactSupport_div {A : Vec3 → Vec3} (hA : HasCompactSupport A) :
    HasCompactSupport (div A) := by
  have hcomp : ∀ i : Fin 3, HasCompactSupport (fun x => pd i (fun y => A y i) x) :=
    fun i => hasCompactSupport_pd (hasCompactSupport_apply hA i) i
  have hsum := HasCompactSupport.finset_sum (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i y => pd i (fun z => A z i) y) (fun i _ => hcomp i)
  have hgoal : div A = fun x => ∑ i : Fin 3, pd i (fun y => A y i) x := rfl
  rw [hgoal, ← Finset.sum_fn]
  exact hsum

/-! ## A smooth compactly supported source with an explicit solution -/

/-- Pointwise vanishing of the derivative left of `0`. -/
theorem deriv_smoothTransition_eq_zero_of_lt_zero {t : ℝ} (h : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have hz : Real.smoothTransition =ᶠ[𝓝 t] 0 := by
    filter_upwards [(isOpen_Iio (a := (0 : ℝ))).mem_nhds (show t ∈ Set.Iio (0 : ℝ) from h)]
      with s hs
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
  simpa using hz.deriv_eq

/-- Pointwise vanishing of the derivative right of `1`. (The function itself tends to `1`, so it
is its *derivative* that is compactly supported, not `smoothTransition`.) -/
theorem deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (h : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have hz : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
    filter_upwards [(isOpen_Ioi (a := (1 : ℝ))).mem_nhds (show t ∈ Set.Ioi (1 : ℝ) from h)]
      with s hs
    exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
  simpa using hz.deriv_eq

/-- `deriv smoothTransition` is supported in `[0,1]`, hence compactly supported. -/
theorem hasCompactSupport_smoothTransition_deriv :
    HasCompactSupport (deriv Real.smoothTransition) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (0 : ℝ) 1) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  by_contra hmem
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  rcases hmem with hlt | hgt
  · exact ht (deriv_smoothTransition_eq_zero_of_lt_zero hlt)
  · exact ht (deriv_smoothTransition_eq_zero_of_one_lt hgt)

/-- `deriv (deriv smoothTransition)` is compactly supported: a smooth compactly supported source. -/
theorem hasCompactSupport_smoothTransition_deriv_deriv :
    HasCompactSupport (deriv (deriv Real.smoothTransition)) :=
  hasCompactSupport_smoothTransition_deriv.deriv

theorem contDiff_one_deriv_smoothTransition : ContDiff ℝ 1 (deriv Real.smoothTransition) := by
  have h2 : ContDiff ℝ (1 + 1) Real.smoothTransition := Real.smoothTransition.contDiff
  rw [contDiff_succ_iff_deriv] at h2
  exact h2.2.2

/-- **Poisson's equation solved for a smooth compactly supported source**: with
`χ = −smoothTransition (x ⬝ᵥ w)/(w ⬝ᵥ w)`, `∇²χ = smoothTransition'' (x ⬝ᵥ w)` everywhere, and the
right-hand side is a smooth compactly supported member of the class in `NewtonianPotentialSolver`. -/
theorem poisson_smoothTransition (w : Vec3) (hw : w ≠ 0) :
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧
      ∀ x, maxwellNabla2 χ x = deriv (deriv Real.smoothTransition) (x ⬝ᵥ w) := by
  have hG : ∀ t, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    fun t => ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) t).hasDerivAt
  have hG1 : ∀ t, HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) t) t :=
    fun t => (contDiff_one_deriv_smoothTransition.differentiable (by norm_num) t).hasDerivAt
  have hg : Continuous (deriv (deriv Real.smoothTransition)) :=
    contDiff_one_deriv_smoothTransition.continuous_deriv le_rfl
  exact poisson_profile hw hG hG1 hg

/-! ## A worked non-vacuous instance of the closed form -/

theorem dotProduct_axis_self (i : Fin 3) : axis i ⬝ᵥ axis i = 1 := by
  simp [axis, dotProduct, Pi.single_apply]

theorem axis_ne_zero (i : Fin 3) : axis i ≠ (0 : Vec3) := by
  intro h
  have := congrFun h i
  simp [axis] at this

/-- The closed form on a concrete field: for `χ = −(x ⬝ᵥ e₀)²/2` the gauge potential formula
`gaugeChi (t²/2) e₀` returns exactly `−(x ⬝ᵥ e₀)²/2`. -/
theorem gaugeChi_linear :
    gaugeChi (fun t : ℝ => t ^ 2 / 2) (axis 0) = fun x : Vec3 => -(x ⬝ᵥ axis 0) ^ 2 / 2 := by
  funext x
  have h1 : axis (0 : Fin 3) ⬝ᵥ axis (0 : Fin 3) = 1 := dotProduct_axis_self 0
  simp only [gaugeChi, h1, div_one]
  ring

/-- **Non-vacuity of the profile class**: the field `𝔄 y = (y ⬝ᵥ e₀) • e₀` has `div 𝔄 = 1`, and
the theorem produces a `C²` `χ` (namely `−(x ⬝ᵥ e₀)²/2`, by `gaugeChi_linear`) with
`div (𝔄 + ∇χ) = 0`. So the class of sources handled here is non-empty and the conclusion is not
the trivial `χ = 0`. -/
theorem gauge_example_linear :
    ∃ χ : Vec3 → ℝ, ContDiff ℝ 2 χ ∧
      ∀ x, div (fun y => (y ⬝ᵥ axis 0) • axis 0 + grad χ y) x = 0 := by
  refine exists_gauge_of_dotProduct (g := fun _ => 1) (G1 := fun t => t) (G := fun t => t ^ 2 / 2)
    (w := axis 0) (axis_ne_zero 0) ?_ ?_ ?_ ?_ continuous_const
  · intro x
    have hfun : ∀ i : Fin 3, pd i (fun y : Vec3 => ((y ⬝ᵥ axis 0) • axis 0) i) x
        = axis 0 i * axis 0 i := by
      intro i
      have hd : DifferentiableAt ℝ (fun y : Vec3 => y ⬝ᵥ axis 0) x :=
        differentiableAt_comp_dotCLM (G := id) (G' := fun _ => (1 : ℝ))
          (fun t => hasDerivAt_id t) (axis 0) x
      have h2 : pd i (fun y : Vec3 => y ⬝ᵥ axis 0) x = axis 0 i := by
        simpa using pd_comp_dotCLM (G := id) (G' := fun _ => (1 : ℝ))
          (fun t => hasDerivAt_id t) (axis 0) x i
      have h3 := pd_const_mul (i := i) (c := axis 0 i) (f := fun y : Vec3 => y ⬝ᵥ axis 0)
        (x := x) hd
      have h4 : (fun y : Vec3 => ((y ⬝ᵥ axis 0) • axis 0) i)
          = fun y => axis 0 i * (y ⬝ᵥ axis 0) := by
        funext y
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [h4, h3, h2]
    rw [div, Finset.sum_congr rfl (fun i _ => hfun i)]
    simp [axis, Pi.single_apply]
  · intro i
    exact fun x => (differentiableAt_comp_dotCLM (G := id) (G' := fun _ => (1 : ℝ))
      (fun t => hasDerivAt_id t) (axis 0) x).mul_const (axis 0 i)
  · intro t
    have h := (hasDerivAt_pow 2 t).div_const 2
    simpa using h
  · intro t
    exact hasDerivAt_id t

end Maxwell
