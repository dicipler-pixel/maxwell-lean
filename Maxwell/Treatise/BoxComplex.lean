/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/
import Maxwell.Treatise.ElectrostaticStress
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Beyond boxes: the divergence theorem on box complexes (Art. 105 on a larger class of regions)

`Maxwell.Treatise.ElectrostaticStress` proves the integrated direct-action test
(`art105_directAction`) on a single box `[a,b]`, because that is what Mathlib's divergence theorem
covers. Maxwell asks it for *any* closed surface (Treatise 1881, vol. I, Art. 105, p. 147).

This file extends the class of regions with no new analysis at all, by **additivity** of the
integral — the surface functional is carried along as a signed sum of face integrals:

* `integral_rowDiv_box` : the base case (Mathlib's `integral_divergence_of_hasFDerivAt_off_countable'`).
* `integral_rowDiv_biUnion` : a finite family of boxes whose pairwise intersections are null.
  Internal faces cancel automatically, so this covers L-shapes, staircases and any polycube
  presented as a union of boxes.
* `integral_rowDiv_sdiff` : a box with an inner box removed (the faces of the hole enter with the
  sign that makes them outward normals of the remaining region); this is also the "cut a small box
  out around a singularity" tool.
* `integral_rowDiv_boxComplex` : finite union of boxes minus finite union of boxes inside it
  ("polycube with holes"), the largest class handled here.

The class of *fields* is weakened as well: neither a global `ContDiff ℝ 2` potential nor a global
Poisson equation is needed, only `ContDiffAt ℝ 2 Ψ x` and `maxwellNabla2 Ψ x = 4π ρ x` **at the
points of the region** (`art105_box`, `art105_boxComplex`). This is what allows a potential with
a singularity outside the region (a point or line charge) to be treated: see
`art105_planeKernel_box`.

Everything here is a theorem about integrals; nothing is assumed.
-/

namespace Maxwell

open MeasureTheory Matrix Filter
open scoped Topology

/-! ## Row fields: the shape in which Mathlib's divergence theorem is stated

Mathlib's `integral_divergence_of_hasFDerivAt_off_countable'` integrates `∑ᵢ ∂ᵢ (f i)`, the
divergence of the row field `i ↦ f i`. `rowDiv` is that divergence and `rowFlux` its signed face
flux, so that both sides of the theorem can be transported between regions. -/

/-- The divergence `∑ᵢ ∂ᵢ (f i)` of the row field `i ↦ f i`. -/
noncomputable def rowDiv (f : Fin 3 → Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∑ i, fderiv ℝ (f i) x (axis i)

/-- The signed face flux of a row field over the six faces of the box `[a,b]`: on `x i = b i` with
the outward normal `+eᵢ`, on `x i = a i` with `−eᵢ`. This is Mathlib's right-hand side. -/
noncomputable def rowFlux (f : Fin 3 → Vec3 → ℝ) (a b : Vec3) : ℝ :=
  ∑ i, ((∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f i (i.insertNth (b i) y)) -
    (∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f i (i.insertNth (a i) y)))

/-- The open box `∏ᵢ (a i, b i)`; the divergence theorem needs differentiability there. -/
def openBox (a b : Vec3) : Set Vec3 := Set.pi Set.univ fun i => Set.Ioo (a i) (b i)

theorem mem_openBox {a b x : Vec3} : x ∈ openBox a b ↔ ∀ i, a i < x i ∧ x i < b i := by
  simp [openBox, Set.mem_pi]

/-- `rowDiv` is the ordinary divergence of the vector field whose components are the row field. -/
theorem rowDiv_eq_div (f : Fin 3 → Vec3 → ℝ) (x : Vec3) :
    rowDiv f x = div (fun x i => f i x) x := rfl

/-- `rowFlux` is Maxwell's `boxSurfaceForce` for the stress whose `k`-th column is the row field. -/
theorem rowFlux_eq_boxSurfaceForce (f : Fin 3 → Vec3 → ℝ) (a b : Vec3) (k : Fin 3) :
    rowFlux f a b = boxSurfaceForce (fun x i _ => f i x) a b k := rfl

/-! ## The base case: one box (Mathlib's divergence theorem) -/

theorem integral_rowDiv_box {f : Fin 3 → Vec3 → ℝ} {a b : Vec3} (hab : a ≤ b)
    (Hc : ∀ i, ContinuousOn (f i) (Set.Icc a b))
    (Hd : ∀ x ∈ openBox a b, ∀ i, DifferentiableAt ℝ (f i) x)
    (Hi : IntegrableOn (rowDiv f) (Set.Icc a b)) :
    ∫ x in Set.Icc a b, rowDiv f x = rowFlux f a b := by
  refine MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable' (n := 2) a b hab f
    (fun i x => fderiv ℝ (f i) x) ∅ Set.countable_empty Hc ?_ Hi
  intro x hx i
  exact (Hd x (mem_openBox.2 (by simpa using hx)) i).hasFDerivAt

/-! ## Additivity: a finite union of boxes with null pairwise intersections -/

/-- A finite union of boxes is measurable. -/
theorem measurableSet_biUnion_boxes (L : Finset (Vec3 × Vec3)) :
    MeasurableSet (⋃ B ∈ L, Set.Icc B.1 B.2) := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | insert a s ha IH => rw [Finset.set_biUnion_insert]; exact measurableSet_Icc.union IH

/-- A finite union of null sets indexed by a finset is null. -/
theorem volume_biUnion_finset_null {L : Finset (Vec3 × Vec3)} {t : Vec3 × Vec3 → Set Vec3}
    (h : ∀ B ∈ L, volume (t B) = 0) : volume (⋃ B ∈ L, t B) = 0 := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | insert a s ha IH =>
    rw [Finset.set_biUnion_insert, measure_union_null_iff]
    exact ⟨h a (Finset.mem_insert_self a s),
      IH fun B hB => h B (Finset.mem_insert_of_mem hB)⟩

/-- If `s` meets each of finitely many boxes in a null set, it meets their union in a null set. -/
theorem volume_inter_biUnion_boxes_null {L : Finset (Vec3 × Vec3)} {s : Set Vec3}
    (h : ∀ B ∈ L, volume (s ∩ Set.Icc B.1 B.2) = 0) :
    volume (s ∩ ⋃ B ∈ L, Set.Icc B.1 B.2) = 0 := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | insert a t ha IH =>
    rw [Finset.set_biUnion_insert, Set.inter_union_distrib_left, measure_union_null_iff]
    exact ⟨h a (Finset.mem_insert_self a t), IH fun B hB => h B (Finset.mem_insert_of_mem hB)⟩

/-- **Divergence theorem on a finite family of boxes.** If the boxes have pairwise null
intersections (in particular if they are disjoint or share only faces), the integral of the
divergence over their union is the sum of the signed face fluxes. For touching boxes the shared
faces cancel, as they must. -/
theorem integral_rowDiv_biUnion (L : Finset (Vec3 × Vec3)) {f : Fin 3 → Vec3 → ℝ}
    (hle : ∀ B ∈ L, B.1 ≤ B.2)
    (hae : ∀ B₁ ∈ L, ∀ B₂ ∈ L, B₁ ≠ B₂ →
      volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0)
    (Hc : ∀ B ∈ L, ∀ i, ContinuousOn (f i) (Set.Icc B.1 B.2))
    (Hd : ∀ B ∈ L, ∀ x ∈ openBox B.1 B.2, ∀ i, DifferentiableAt ℝ (f i) x)
    (Hi : ∀ B ∈ L, IntegrableOn (rowDiv f) (Set.Icc B.1 B.2)) :
    ∫ x in (⋃ B ∈ L, Set.Icc B.1 B.2), rowDiv f x = ∑ B ∈ L, rowFlux f B.1 B.2 := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | insert B₀ L hB₀ IH =>
    have hleL : ∀ B ∈ L, B.1 ≤ B.2 := fun B hB => hle B (Finset.mem_insert_of_mem hB)
    have haeL : ∀ B₁ ∈ L, ∀ B₂ ∈ L, B₁ ≠ B₂ →
        volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0 := fun B₁ h₁ B₂ h₂ =>
      hae B₁ (Finset.mem_insert_of_mem h₁) B₂ (Finset.mem_insert_of_mem h₂)
    have HcL : ∀ B ∈ L, ∀ i, ContinuousOn (f i) (Set.Icc B.1 B.2) :=
      fun B hB => Hc B (Finset.mem_insert_of_mem hB)
    have HdL : ∀ B ∈ L, ∀ x ∈ openBox B.1 B.2, ∀ i, DifferentiableAt ℝ (f i) x :=
      fun B hB => Hd B (Finset.mem_insert_of_mem hB)
    have HiL : ∀ B ∈ L, IntegrableOn (rowDiv f) (Set.Icc B.1 B.2) :=
      fun B hB => Hi B (Finset.mem_insert_of_mem hB)
    have IH' := IH hleL haeL HcL HdL HiL
    rw [Finset.set_biUnion_insert, Finset.sum_insert hB₀]
    have hnull : volume (Set.Icc B₀.1 B₀.2 ∩ ⋃ B ∈ L, Set.Icc B.1 B.2) = 0 :=
      volume_inter_biUnion_boxes_null fun B hB =>
        hae B₀ (Finset.mem_insert_self B₀ L) B (Finset.mem_insert_of_mem hB)
          (fun h => hB₀ (h ▸ hB))
    have hint : IntegrableOn (rowDiv f) (⋃ B ∈ L, Set.Icc B.1 B.2) :=
      integrableOn_finset_iUnion.2 HiL
    have hnull' : volume ((⋃ B ∈ L, Set.Icc B.1 B.2) ∩ Set.Icc B₀.1 B₀.2) = 0 := by
      rw [Set.inter_comm]; exact hnull
    rw [Set.union_comm,
      setIntegral_union₀ hnull' measurableSet_Icc.nullMeasurableSet hint
        (Hi B₀ (Finset.mem_insert_self B₀ L)),
      IH',
      integral_rowDiv_box (hle B₀ (Finset.mem_insert_self B₀ L))
        (Hc B₀ (Finset.mem_insert_self B₀ L)) (Hd B₀ (Finset.mem_insert_self B₀ L))
        (Hi B₀ (Finset.mem_insert_self B₀ L)), add_comm]

/-! ## A box with an inner box removed -/

/-- **Divergence theorem on a box with a hole.** For `[c,d] ⊆ [a,b]` the integral of the
divergence over `[a,b] \ [c,d]` is the outer face flux minus the inner face flux: the faces of the
hole carry the outward normal of the remaining region. -/
theorem integral_rowDiv_sdiff {f : Fin 3 → Vec3 → ℝ} {a b c d : Vec3}
    (hab : a ≤ b) (hcd : c ≤ d) (hsub : Set.Icc c d ⊆ Set.Icc a b)
    (Hc : ∀ i, ContinuousOn (f i) (Set.Icc a b))
    (Hd : ∀ x ∈ openBox a b, ∀ i, DifferentiableAt ℝ (f i) x)
    (Hc' : ∀ i, ContinuousOn (f i) (Set.Icc c d))
    (Hd' : ∀ x ∈ openBox c d, ∀ i, DifferentiableAt ℝ (f i) x)
    (Hi : IntegrableOn (rowDiv f) (Set.Icc a b)) :
    ∫ x in (Set.Icc a b \ Set.Icc c d), rowDiv f x = rowFlux f a b - rowFlux f c d := by
  rw [setIntegral_sdiff₀ measurableSet_Icc.nullMeasurableSet Hi hsub,
    integral_rowDiv_box hab Hc Hd Hi, integral_rowDiv_box hcd Hc' Hd' (Hi.mono_set hsub)]

/-! ## Polycubes with holes: a finite union of boxes minus a finite union of boxes -/

/-- **Divergence theorem on a box complex**: a finite union of boxes (`O`, with pairwise null
intersections) with a finite union of boxes (`H`, likewise) removed from it. The surface
functional is the sum of the outer face fluxes minus the sum of the face fluxes of the holes. -/
theorem integral_rowDiv_boxComplex (O H : Finset (Vec3 × Vec3)) {f : Fin 3 → Vec3 → ℝ}
    (hOle : ∀ B ∈ O, B.1 ≤ B.2) (hHle : ∀ B ∈ H, B.1 ≤ B.2)
    (hOae : ∀ B₁ ∈ O, ∀ B₂ ∈ O, B₁ ≠ B₂ →
      volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0)
    (hHae : ∀ B₁ ∈ H, ∀ B₂ ∈ H, B₁ ≠ B₂ →
      volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0)
    (hsub : (⋃ B ∈ H, Set.Icc B.1 B.2) ⊆ (⋃ B ∈ O, Set.Icc B.1 B.2))
    (Hc : ∀ B ∈ O, ∀ i, ContinuousOn (f i) (Set.Icc B.1 B.2))
    (Hd : ∀ B ∈ O, ∀ x ∈ openBox B.1 B.2, ∀ i, DifferentiableAt ℝ (f i) x)
    (HcH : ∀ B ∈ H, ∀ i, ContinuousOn (f i) (Set.Icc B.1 B.2))
    (HdH : ∀ B ∈ H, ∀ x ∈ openBox B.1 B.2, ∀ i, DifferentiableAt ℝ (f i) x)
    (Hi : ∀ B ∈ O, IntegrableOn (rowDiv f) (Set.Icc B.1 B.2))
    (HiH : ∀ B ∈ H, IntegrableOn (rowDiv f) (Set.Icc B.1 B.2)) :
    ∫ x in ((⋃ B ∈ O, Set.Icc B.1 B.2) \ (⋃ B ∈ H, Set.Icc B.1 B.2)), rowDiv f x
      = (∑ B ∈ O, rowFlux f B.1 B.2) - ∑ B ∈ H, rowFlux f B.1 B.2 := by
  have hiO : IntegrableOn (rowDiv f) (⋃ B ∈ O, Set.Icc B.1 B.2) :=
    integrableOn_finset_iUnion.2 Hi
  rw [setIntegral_sdiff₀ (measurableSet_biUnion_boxes H).nullMeasurableSet hiO hsub,
    integral_rowDiv_biUnion O hOle hOae Hc Hd Hi,
    integral_rowDiv_biUnion H hHle hHae HcH HdH HiH]


/-! ## Art. 105 with Poisson's equation required only on the region

`Maxwell.Art105DirectAction` assumes a globally `C²` potential with `∇²Ψ = 4πρ` everywhere. That
excludes the potentials of point and line charges, whose singularities lie outside the region of
interest. The results below assume `ContDiffAt ℝ 2 Ψ x` and `∇²Ψ x = 4π ρ x` only at the points of
the region, and `ρ` continuous there. -/

/-- The local Art. 105 hypothesis on a set `s`: `Ψ` is `C²` at each point of `s`, Poisson's
equation `∇²Ψ = 4πρ` holds there (Maxwell's sign), and `ρ` is continuous there. -/
def IsStressPotentialOn (Ψ : Vec3 → ℝ) (ρ : Vec3 → ℝ) (s : Set Vec3) : Prop :=
  (∀ x ∈ s, ContDiffAt ℝ 2 Ψ x) ∧ (∀ x ∈ s, maxwellNabla2 Ψ x = fourPi * ρ x) ∧
    ContinuousOn ρ s

theorem IsStressPotentialOn.mono {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ} {s t : Set Vec3}
    (H : IsStressPotentialOn Ψ ρ s) (h : t ⊆ s) : IsStressPotentialOn Ψ ρ t :=
  ⟨fun x hx => H.1 x (h hx), fun x hx => H.2.1 x (h hx), H.2.2.mono h⟩

/-- The force per unit volume `ρ • E`, `E = −∇Ψ`, of the electromotive intensity. -/
noncomputable def forceDensity (Ψ : Vec3 → ℝ) (ρ : Vec3 → ℝ) (x : Vec3) : Vec3 :=
  ρ x • (-grad Ψ x)

/-- The `k`-th column of the stress of a potential, as a row field for the divergence theorem. -/
noncomputable def stressRowField (Ψ : Vec3 → ℝ) (k : Fin 3) : Fin 3 → Vec3 → ℝ :=
  fun i x => stress1881 Ψ x i k

theorem rowDiv_stressRowField (Ψ : Vec3 → ℝ) (k : Fin 3) (x : Vec3) :
    rowDiv (stressRowField Ψ k) x = stressForce (stress1881 Ψ) x k := rfl

theorem rowFlux_stressRowField (Ψ : Vec3 → ℝ) (k : Fin 3) (a b : Vec3) :
    rowFlux (stressRowField Ψ k) a b = boxSurfaceForce (stress1881 Ψ) a b k := rfl

/-- **Pointwise Art. 105** (the repo's `art105_force`), in the form used below. -/
theorem art105_pointwise {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ} {x : Vec3}
    (hΨ : ContDiffAt ℝ 2 Ψ x) (hP : maxwellNabla2 Ψ x = fourPi * ρ x) (k : Fin 3) :
    forceDensity Ψ ρ x k = rowDiv (stressRowField Ψ k) x := by
  rw [rowDiv_stressRowField, forceDensity, Pi.smul_apply, smul_eq_mul]
  exact (congrFun (art105_force hΨ hP) k).symm

theorem continuousOn_grad_apply {Ψ : Vec3 → ℝ} {s : Set Vec3}
    (hΨ : ∀ x ∈ s, ContDiffAt ℝ 2 Ψ x) (j : Fin 3) :
    ContinuousOn (fun y => grad Ψ y j) s :=
  fun x hx =>
    (((hΨ x hx).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).continuousWithinAt

theorem contDiffAt_stress1881_apply {Ψ : Vec3 → ℝ} {x : Vec3} (hΨ : ContDiffAt ℝ 2 Ψ x)
    (h k : Fin 3) : ContDiffAt ℝ 1 (fun y => stress1881 Ψ y h k) x := by
  have hg : ∀ j, ContDiffAt ℝ 1 (fun y => grad Ψ y j) x := fun j =>
    (hΨ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have h0 := hg 0; have h1 := hg 1; have h2 := hg 2; have hh := hg h; have hk := hg k
  simp only [stress1881, componentForm, sq_eq, δ]
  fun_prop

theorem continuousOn_stress1881_apply {Ψ : Vec3 → ℝ} {s : Set Vec3}
    (hΨ : ∀ x ∈ s, ContDiffAt ℝ 2 Ψ x) (h k : Fin 3) :
    ContinuousOn (fun y => stress1881 Ψ y h k) s :=
  fun x hx => (contDiffAt_stress1881_apply (hΨ x hx) h k).continuousAt.continuousWithinAt

/-- The force density is integrable on a box on which the local Art. 105 hypothesis holds. -/
theorem integrableOn_forceDensity {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ} {a b : Vec3}
    (H : IsStressPotentialOn Ψ ρ (Set.Icc a b)) (k : Fin 3) :
    IntegrableOn (fun x => forceDensity Ψ ρ x k) (Set.Icc a b) := by
  have hg := (continuousOn_grad_apply H.1 k).neg
  have hcont : ContinuousOn (fun x => ρ x * (-(grad Ψ x k))) (Set.Icc a b) := H.2.2.mul hg
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  simpa [forceDensity, Pi.smul_apply, smul_eq_mul] using hcont

/-- The `C¹` and integrability data for the stress row field on a box, from the local hypothesis. -/
theorem stressRowField_continuousOn {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ} {a b : Vec3}
    (H : IsStressPotentialOn Ψ ρ (Set.Icc a b)) (k : Fin 3) :
    ∀ i, ContinuousOn (stressRowField Ψ k i) (Set.Icc a b) := fun i =>
  continuousOn_stress1881_apply H.1 i k

theorem stressRowField_differentiableAt {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ} {a b : Vec3}
    (H : IsStressPotentialOn Ψ ρ (Set.Icc a b)) (k : Fin 3) :
    ∀ x ∈ openBox a b, ∀ i, DifferentiableAt ℝ (stressRowField Ψ k i) x := by
  intro x hx i
  have hx' : x ∈ Set.Icc a b := by
    rw [mem_openBox] at hx
    exact ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩
  exact (contDiffAt_stress1881_apply (H.1 x hx') i k).differentiableAt (by norm_num)

theorem stressRowField_integrableOn {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ} {a b : Vec3}
    (H : IsStressPotentialOn Ψ ρ (Set.Icc a b)) (k : Fin 3) :
    IntegrableOn (rowDiv (stressRowField Ψ k)) (Set.Icc a b) :=
  (integrableOn_forceDensity H k).congr_fun
    (fun x hx => art105_pointwise (H.1 x hx) (H.2.1 x hx) k) measurableSet_Icc

/-- **Art. 105 on a box, with the Poisson equation assumed only on the box.** -/
theorem art105_box {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ} {a b : Vec3} (hab : a ≤ b)
    (H : IsStressPotentialOn Ψ ρ (Set.Icc a b)) (k : Fin 3) :
    ∫ x in Set.Icc a b, forceDensity Ψ ρ x k = boxSurfaceForce (stress1881 Ψ) a b k := by
  rw [setIntegral_congr_fun measurableSet_Icc
      (fun x hx => art105_pointwise (H.1 x hx) (H.2.1 x hx) k),
    integral_rowDiv_box hab (stressRowField_continuousOn H k) (stressRowField_differentiableAt H k)
      (stressRowField_integrableOn H k),
    rowFlux_stressRowField]

/-- **Art. 105 on a finite union of boxes** with pairwise null intersections (L-shapes,
staircases, polycubes). -/
theorem art105_biUnion (L : Finset (Vec3 × Vec3)) {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ}
    (hle : ∀ B ∈ L, B.1 ≤ B.2)
    (hae : ∀ B₁ ∈ L, ∀ B₂ ∈ L, B₁ ≠ B₂ →
      volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0)
    (H : ∀ B ∈ L, IsStressPotentialOn Ψ ρ (Set.Icc B.1 B.2)) (k : Fin 3) :
    ∫ x in (⋃ B ∈ L, Set.Icc B.1 B.2), forceDensity Ψ ρ x k
      = ∑ B ∈ L, boxSurfaceForce (stress1881 Ψ) B.1 B.2 k := by
  have hpt : ∀ x ∈ (⋃ B ∈ L, Set.Icc B.1 B.2),
      forceDensity Ψ ρ x k = rowDiv (stressRowField Ψ k) x := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨B, hx'⟩ := hx
    rw [Set.mem_iUnion] at hx'
    obtain ⟨hB, hxB⟩ := hx'
    obtain ⟨hΨ, hP, -⟩ := H B hB
    exact art105_pointwise (hΨ x hxB) (hP x hxB) k
  rw [setIntegral_congr_fun (measurableSet_biUnion_boxes L) hpt,
    integral_rowDiv_biUnion L hle hae (fun B hB => stressRowField_continuousOn (H B hB) k)
      (fun B hB => stressRowField_differentiableAt (H B hB) k)
      (fun B hB => stressRowField_integrableOn (H B hB) k)]
  simp only [rowFlux_stressRowField]

/-- **Art. 105 on a box with a hole.** -/
theorem art105_sdiff {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ} {a b c d : Vec3}
    (hab : a ≤ b) (hcd : c ≤ d) (hsub : Set.Icc c d ⊆ Set.Icc a b)
    (H : IsStressPotentialOn Ψ ρ (Set.Icc a b)) (k : Fin 3) :
    ∫ x in (Set.Icc a b \ Set.Icc c d), forceDensity Ψ ρ x k
      = boxSurfaceForce (stress1881 Ψ) a b k - boxSurfaceForce (stress1881 Ψ) c d k := by
  have H' : IsStressPotentialOn Ψ ρ (Set.Icc c d) := H.mono hsub
  rw [setIntegral_congr_fun (measurableSet_Icc.diff measurableSet_Icc)
      (fun x hx => art105_pointwise (H.1 x hx.1) (H.2.1 x hx.1) k),
    integral_rowDiv_sdiff hab hcd hsub (stressRowField_continuousOn H k)
      (stressRowField_differentiableAt H k) (stressRowField_continuousOn H' k)
      (stressRowField_differentiableAt H' k) (stressRowField_integrableOn H k),
    rowFlux_stressRowField, rowFlux_stressRowField]

/-- **Art. 105 on a box complex**: a finite union of boxes with a finite union of boxes removed
from it. -/
theorem art105_boxComplex (O Hh : Finset (Vec3 × Vec3)) {Ψ : Vec3 → ℝ} {ρ : Vec3 → ℝ}
    (hOle : ∀ B ∈ O, B.1 ≤ B.2) (hHle : ∀ B ∈ Hh, B.1 ≤ B.2)
    (hOae : ∀ B₁ ∈ O, ∀ B₂ ∈ O, B₁ ≠ B₂ →
      volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0)
    (hHae : ∀ B₁ ∈ Hh, ∀ B₂ ∈ Hh, B₁ ≠ B₂ →
      volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0)
    (hsub : (⋃ B ∈ Hh, Set.Icc B.1 B.2) ⊆ (⋃ B ∈ O, Set.Icc B.1 B.2))
    (HO : ∀ B ∈ O, IsStressPotentialOn Ψ ρ (Set.Icc B.1 B.2))
    (HH : ∀ B ∈ Hh, IsStressPotentialOn Ψ ρ (Set.Icc B.1 B.2)) (k : Fin 3) :
    ∫ x in ((⋃ B ∈ O, Set.Icc B.1 B.2) \ (⋃ B ∈ Hh, Set.Icc B.1 B.2)),
        forceDensity Ψ ρ x k
      = (∑ B ∈ O, boxSurfaceForce (stress1881 Ψ) B.1 B.2 k)
        - ∑ B ∈ Hh, boxSurfaceForce (stress1881 Ψ) B.1 B.2 k := by
  have hpt : ∀ x ∈ ((⋃ B ∈ O, Set.Icc B.1 B.2) \ (⋃ B ∈ Hh, Set.Icc B.1 B.2)),
      forceDensity Ψ ρ x k = rowDiv (stressRowField Ψ k) x := by
    intro x hx
    obtain ⟨hx1, -⟩ := hx
    rw [Set.mem_iUnion] at hx1
    obtain ⟨B, hx'⟩ := hx1
    rw [Set.mem_iUnion] at hx'
    obtain ⟨hB, hxB⟩ := hx'
    obtain ⟨hΨ, hP, -⟩ := HO B hB
    exact art105_pointwise (hΨ x hxB) (hP x hxB) k
  rw [setIntegral_congr_fun
      ((measurableSet_biUnion_boxes O).diff (measurableSet_biUnion_boxes Hh)) hpt,
    integral_rowDiv_boxComplex O Hh hOle hHle hOae hHae hsub
      (fun B hB => stressRowField_continuousOn (HO B hB) k)
      (fun B hB => stressRowField_differentiableAt (HO B hB) k)
      (fun B hB => stressRowField_continuousOn (HH B hB) k)
      (fun B hB => stressRowField_differentiableAt (HH B hB) k)
      (fun B hB => stressRowField_integrableOn (HO B hB) k)
      (fun B hB => stressRowField_integrableOn (HH B hB) k)]
  simp only [rowFlux_stressRowField]


/-! ## Concrete instances: the hypotheses are satisfiable, and the regions are not boxes -/

/-- `pd` of a coordinate function. -/
theorem pd_coord_apply (i j : Fin 3) (x : Vec3) : pd i (fun y : Vec3 => y j) x = δ i j := by
  have h : HasFDerivAt (fun y : Vec3 => y j) (ContinuousLinearMap.proj j) x :=
    (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).hasFDerivAt
  rw [pd, h.fderiv]
  simp [ContinuousLinearMap.proj_apply, axis, δ, Pi.single_apply, eq_comm]

/-- Chain rule for `pd` along a scalar outer function. -/
theorem pd_comp {g : ℝ → ℝ} {g' : ℝ} {f : Vec3 → ℝ} {x : Vec3} (i : Fin 3)
    (hg : HasDerivAt g g' (f x)) (hf : DifferentiableAt ℝ f x) :
    pd i (fun y => g (f y)) x = g' * pd i f x := by
  have h := hg.comp_hasFDerivAt x hf.hasFDerivAt
  rw [pd]
  change fderiv ℝ (g ∘ f) x (axis i) = g' * pd i f x
  rw [h.fderiv, _root_.smul_apply, smul_eq_mul, pd]

theorem pd_sq_apply (i : Fin 3) (x : Vec3) : pd i (fun y : Vec3 => sq y) x = 2 * x i := by
  have h : (fun y : Vec3 => sq y) = fun y => y 0 * y 0 + y 1 * y 1 + y 2 * y 2 := by
    funext y; rw [sq_eq]; ring
  rw [h, pd_add _ (by fun_prop) (by fun_prop), pd_add _ (by fun_prop) (by fun_prop),
    pd_mul i (by fun_prop) (by fun_prop), pd_mul i (by fun_prop) (by fun_prop),
    pd_mul i (by fun_prop) (by fun_prop)]
  simp only [pd_coord_apply]
  fin_cases i <;> simp [δ, Fin.ext_iff] <;> ring

/-- `x ↦ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2` has Maxwell's `∇² = −6`. -/
theorem maxwellNabla2_sq (x : Vec3) : maxwellNabla2 (fun y : Vec3 => sq y) x = -6 := by
  have h : ∀ i : Fin 3, pd i (fun y => pd i (fun z : Vec3 => sq z) y) x = 2 := by
    intro i
    have e : (fun y : Vec3 => pd i (fun z : Vec3 => sq z) y) = fun y => 2 * y i := by
      funext y; exact pd_sq_apply i y
    rw [e, pd_const_mul i 2 (by fun_prop), pd_coord_apply]
    simp [δ]
  simp only [maxwellNabla2, Fin.sum_univ_three, h]
  norm_num

/-- The quadratic potential with its charge density: `∇²(sq) = −6 = 4πρ`. -/
theorem isStressPotentialOn_sq (a b : Vec3) :
    IsStressPotentialOn (fun x : Vec3 => sq x) (fun _ => -(3 / (2 * Real.pi)))
      (Set.Icc a b) := by
  refine ⟨fun x _ => ?_, fun x _ => ?_, continuous_const.continuousOn⟩
  · have h : (fun y : Vec3 => sq y) = fun y => y 0 * y 0 + y 1 * y 1 + y 2 * y 2 := by
      funext y; rw [sq_eq]; ring
    rw [h]; fun_prop
  · rw [maxwellNabla2_sq]
    have hpi := Real.pi_ne_zero
    simp only [fourPi]
    field_simp
    ring

/-- **A concrete box**: the quadratic potential on any box, with `ρ = −3/2π`. -/
theorem art105_sqBox (a b : Vec3) (hab : a ≤ b) (k : Fin 3) :
    ∫ x in Set.Icc a b,
        forceDensity (fun x : Vec3 => sq x) (fun _ => -(3 / (2 * Real.pi))) x k
      = boxSurfaceForce (stress1881 (fun x : Vec3 => sq x)) a b k :=
  art105_box hab (isStressPotentialOn_sq a b) k

/-! ### Which box pairs have null intersection

Two boxes that touch along a face intersect in a null set, so `art105_biUnion` applies to
L-shapes. -/

theorem volume_coord_eq_zero (i : Fin 3) (c : ℝ) : volume {x : Vec3 | x i = c} = 0 := by
  have h : {x : Vec3 | x i = c} = Set.pi Set.univ (fun j => if j = i then {c} else Set.univ) := by
    ext x
    simp [Set.mem_pi]
  rw [h, volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- Boxes whose `i`-th intervals meet in at most a point have null intersection. -/
theorem volume_Icc_inter_Icc_eq_zero {a b c d : Vec3} {i : Fin 3} (h : b i ≤ c i) :
    volume (Set.Icc a b ∩ Set.Icc c d) = 0 := by
  refine measure_mono_null ?_ (volume_coord_eq_zero i (c i))
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  simp only [Set.mem_Icc] at hx1 hx2
  exact le_antisymm ((hx1.2 i).trans h) (hx2.1 i)


/-- **A concrete non-box region: a staircase.** Two unit cubes glued along an edge,
`[0,1]³ ∪ ([1,2]×[1,2]×[0,1])`. `art105_biUnion` covers it; no single box equals it
(`staircase_not_box`). -/
theorem art105_staircase (k : Fin 3) :
    ∫ x in (Set.Icc (0 : Vec3) 1 ∪ Set.Icc ![1, 1, 0] ![2, 2, 1]),
        forceDensity (fun x : Vec3 => sq x) (fun _ => -(3 / (2 * Real.pi))) x k
      = boxSurfaceForce (stress1881 (fun x : Vec3 => sq x)) (0 : Vec3) 1 k
        + boxSurfaceForce (stress1881 (fun x : Vec3 => sq x)) ![1, 1, 0] ![2, 2, 1] k := by
  set L : Finset (Vec3 × Vec3) :=
    {((0 : Vec3), 1), ((![1, 1, 0] : Vec3), ![2, 2, 1])} with hL
  have hle : ∀ B ∈ L, B.1 ≤ B.2 := by
    intro B hB
    simp only [hL, Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl
    · intro i; norm_num
    · intro i; fin_cases i <;> norm_num
  have hae : ∀ B₁ ∈ L, ∀ B₂ ∈ L, B₁ ≠ B₂ →
      volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0 := by
    intro B₁ h₁ B₂ h₂ hne
    simp only [hL, Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · exact absurd rfl hne
    · exact volume_Icc_inter_Icc_eq_zero (i := 0) (by norm_num)
    · rw [Set.inter_comm]; exact volume_Icc_inter_Icc_eq_zero (i := 0) (by norm_num)
    · exact absurd rfl hne
  have h := art105_biUnion L hle hae (fun B _ => isStressPotentialOn_sq B.1 B.2) k
  rw [hL] at h
  have hne : ((0 : Vec3), (1 : Vec3)) ≠ ((![1, 1, 0] : Vec3), ![2, 2, 1]) := by
    intro hh
    have h0 := congrArg (fun B : Vec3 × Vec3 => B.2 0) hh
    norm_num at h0
  rw [Finset.sum_pair hne] at h
  simpa using h

/-- **The staircase is not a box**: the point `(1/2, 3/2, 1/2)` of the enclosing box
`[0,2]×[0,2]×[0,1]` is in neither cube. -/
theorem staircase_not_box :
    ∃ x : Vec3, x ∈ Set.Icc (0 : Vec3) ![2, 2, 1] ∧
      x ∉ (Set.Icc (0 : Vec3) 1 ∪ Set.Icc ![1, 1, 0] ![2, 2, 1]) := by
  refine ⟨![1 / 2, 3 / 2, 1 / 2], ?_, ?_⟩
  · simp only [Set.mem_Icc]; constructor <;> intro i <;> fin_cases i <;> norm_num
  · intro hx
    rcases hx with hx | hx
    · have h1 := hx.2 1; norm_num at h1
    · have h0 := hx.1 0; norm_num at h0


/-! ## A potential that is `C²` on the region but not on all of space

`planeKernel x = 1/x₀` is `C^∞` off the plane `x₀ = 0` and not even continuous on it, so
`Maxwell.Art105DirectAction` (which assumes `ContDiff ℝ 2 Ψ` globally) cannot be applied to any
region, while `art105_box` applies to every box with `x₀ ≠ 0` there. -/

/-- `1 / x₀`. -/
noncomputable def planeKernel (x : Vec3) : ℝ := (x 0)⁻¹

theorem contDiffAt_planeKernel {x : Vec3} (h : x 0 ≠ 0) : ContDiffAt ℝ 2 planeKernel x := by
  have h0 : ContDiffAt ℝ 2 (fun y : Vec3 => y 0) x := by fun_prop
  exact h0.inv h

theorem pd_planeKernel_zero {x : Vec3} (h : x 0 ≠ 0) :
    pd 0 planeKernel x = -((x 0 ^ 2)⁻¹) := by
  have hd : HasDerivAt (fun t : ℝ => t⁻¹) (-((x 0) ^ 2)⁻¹) (x 0) := hasDerivAt_inv h
  have hc := pd_comp (g := fun t : ℝ => t⁻¹) (g' := -((x 0) ^ 2)⁻¹)
    (f := fun y : Vec3 => y 0) (i := 0) hd (by fun_prop)
  show pd 0 (fun y : Vec3 => (y 0)⁻¹) x = _
  simpa [pd_coord_apply, δ] using hc

theorem pd_planeKernel_one {x : Vec3} (h : x 0 ≠ 0) : pd 1 planeKernel x = 0 := by
  have hd : HasDerivAt (fun t : ℝ => t⁻¹) (-((x 0) ^ 2)⁻¹) (x 0) := hasDerivAt_inv h
  have hc := pd_comp (g := fun t : ℝ => t⁻¹) (g' := -((x 0) ^ 2)⁻¹)
    (f := fun y : Vec3 => y 0) (i := 1) hd (by fun_prop)
  show pd 1 (fun y : Vec3 => (y 0)⁻¹) x = _
  simpa [pd_coord_apply, δ] using hc

theorem pd_planeKernel_two {x : Vec3} (h : x 0 ≠ 0) : pd 2 planeKernel x = 0 := by
  have hd : HasDerivAt (fun t : ℝ => t⁻¹) (-((x 0) ^ 2)⁻¹) (x 0) := hasDerivAt_inv h
  have hc := pd_comp (g := fun t : ℝ => t⁻¹) (g' := -((x 0) ^ 2)⁻¹)
    (f := fun y : Vec3 => y 0) (i := 2) hd (by fun_prop)
  show pd 2 (fun y : Vec3 => (y 0)⁻¹) x = _
  simpa [pd_coord_apply, δ] using hc

theorem pd_pd_planeKernel_zero {x : Vec3} (h : x 0 ≠ 0) :
    pd 0 (fun y => pd 0 planeKernel y) x = ((x 0 ^ 2) ^ 2)⁻¹ * (2 * x 0) := by
  have hev : (fun y => pd 0 planeKernel y) =ᶠ[𝓝 x] fun y => -((y 0 ^ 2)⁻¹) := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually_ne h] with y hy
    exact pd_planeKernel_zero hy
  show fderiv ℝ (fun y => pd 0 planeKernel y) x (axis 0) = _
  rw [hev.fderiv_eq]
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x 0) (x 0) := by
    have h' := hasDerivAt_pow 2 (x 0)
    simpa using h'
  have hg : HasDerivAt (fun t : ℝ => -((t ^ 2)⁻¹)) (-(-(2 * x 0) / (x 0 ^ 2) ^ 2)) (x 0) :=
    (h2.inv (pow_ne_zero 2 h)).neg
  have hd : DifferentiableAt ℝ (fun y : Vec3 => y 0) x := by fun_prop
  have hcomp := hg.comp_hasFDerivAt x hd.hasFDerivAt
  change fderiv ℝ ((fun t : ℝ => -((t ^ 2)⁻¹)) ∘ (fun y : Vec3 => y 0)) x (axis 0) = _
  rw [hcomp.fderiv, _root_.smul_apply, smul_eq_mul]
  have hpd : (fderiv ℝ (fun y : Vec3 => y 0) x) (axis 0) = 1 := by
    have h1 := pd_coord_apply 0 0 x
    simpa [pd, δ] using h1
  rw [hpd, mul_one]
  have hx := h
  field_simp

theorem pd_pd_planeKernel_one {x : Vec3} (h : x 0 ≠ 0) :
    pd 1 (fun y => pd 1 planeKernel y) x = 0 := by
  have hev : (fun y => pd 1 planeKernel y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually_ne h] with y hy
    exact pd_planeKernel_one hy
  show fderiv ℝ (fun y => pd 1 planeKernel y) x (axis 1) = 0
  rw [hev.fderiv_eq]
  simp

theorem pd_pd_planeKernel_two {x : Vec3} (h : x 0 ≠ 0) :
    pd 2 (fun y => pd 2 planeKernel y) x = 0 := by
  have hev : (fun y => pd 2 planeKernel y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually_ne h] with y hy
    exact pd_planeKernel_two hy
  show fderiv ℝ (fun y => pd 2 planeKernel y) x (axis 2) = 0
  rw [hev.fderiv_eq]
  simp

/-- `∇²(1/x₀) = 2/x₀³`, Maxwell's sign: `maxwellNabla2 planeKernel x = −2/x₀³`. -/
theorem maxwellNabla2_planeKernel {x : Vec3} (h : x 0 ≠ 0) :
    maxwellNabla2 planeKernel x = -2 * (x 0 ^ 3)⁻¹ := by
  have h0 := pd_pd_planeKernel_zero h
  have h1 := pd_pd_planeKernel_one h
  have h2 := pd_pd_planeKernel_two h
  simp only [maxwellNabla2, Fin.sum_univ_three, h0, h1, h2]
  have hx := h
  field_simp
  ring

/-- The charge density of `1/x₀` with Maxwell's sign: `∇²Ψ = 4πρ`. -/
noncomputable def planeKernelDensity (x : Vec3) : ℝ := -(1 / (2 * Real.pi)) * (x 0 ^ 3)⁻¹

theorem isStressPotentialOn_planeKernel {a b : Vec3}
    (h : ∀ x ∈ Set.Icc a b, x 0 ≠ 0) :
    IsStressPotentialOn planeKernel planeKernelDensity (Set.Icc a b) := by
  refine ⟨fun x hx => contDiffAt_planeKernel (h x hx), fun x hx => ?_, ?_⟩
  · rw [maxwellNabla2_planeKernel (h x hx)]
    simp only [planeKernelDensity, fourPi]
    have hx' := h x hx
    field_simp
    norm_num
  · refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ ?_ fun x hx => pow_ne_zero 3 (h x hx)
    exact ((continuous_apply 0).continuousOn).pow 3

/-- **Art. 105 for a potential singular outside the box**: `Ψ = 1/x₀` on any box with `x₀ ≠ 0`.
The repository's `Art105DirectAction` cannot be instantiated with this `Ψ`, which is not `C²`
on all of `ℝ³`. -/
theorem art105_planeKernel_box {a b : Vec3} (hab : a ≤ b)
    (h : ∀ x ∈ Set.Icc a b, x 0 ≠ 0) (k : Fin 3) :
    ∫ x in Set.Icc a b, forceDensity planeKernel planeKernelDensity x k
      = boxSurfaceForce (stress1881 planeKernel) a b k :=
  art105_box hab (isStressPotentialOn_planeKernel h) k

/-- `1/x₀` is not `C²` on `ℝ³`: it is not even continuous at `0`. -/
theorem not_contDiff_planeKernel : ¬ ContDiff ℝ 2 planeKernel := by
  intro h
  have hcont : ContinuousAt planeKernel 0 := h.continuous.continuousAt
  have h1 : Tendsto (fun t : ℝ => planeKernel (t • axis 0)) (𝓝[>] 0) atTop := by
    have e : ∀ t : ℝ, planeKernel (t • axis 0) = t⁻¹ := by
      intro t; simp [planeKernel, axis]
    simpa only [e] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  have hsm : Tendsto (fun t : ℝ => t • axis 0) (𝓝[>] (0 : ℝ)) (𝓝 (0 : Vec3)) := by
    have h' : Tendsto (fun t : ℝ => t • axis 0) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) • axis 0)) :=
      tendsto_id.smul_const (axis 0)
    simpa using h'.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t : ℝ => planeKernel (t • axis 0)) (𝓝[>] 0) (𝓝 (planeKernel 0)) :=
    hcont.tendsto.comp hsm
  exact not_tendsto_atTop_of_tendsto_nhds h2 h1


/-! ## Additivity of the integral over a null-intersecting family of boxes

The pure-integration form of the region extension: if a function has integral `Φ B` on each box `B`
of a finite family with pairwise null intersections, its integral over the union is `∑ Φ B`. No
differentiability is involved, so it applies to Maxwell's `AccountedForByStress` directly. -/

/-- **Additivity over a null-intersecting family of boxes.** -/
theorem setIntegral_biUnion_boxes {g : Vec3 → ℝ} (L : Finset (Vec3 × Vec3))
    {Φ : Vec3 × Vec3 → ℝ}
    (hae : ∀ B₁ ∈ L, ∀ B₂ ∈ L, B₁ ≠ B₂ →
      volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0)
    (hi : ∀ B ∈ L, IntegrableOn g (Set.Icc B.1 B.2))
    (hbox : ∀ B ∈ L, ∫ x in Set.Icc B.1 B.2, g x = Φ B) :
    ∫ x in (⋃ B ∈ L, Set.Icc B.1 B.2), g x = ∑ B ∈ L, Φ B := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | insert B₀ L hB₀ IH =>
    have haeL : ∀ B₁ ∈ L, ∀ B₂ ∈ L, B₁ ≠ B₂ →
        volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0 := fun B₁ h₁ B₂ h₂ =>
      hae B₁ (Finset.mem_insert_of_mem h₁) B₂ (Finset.mem_insert_of_mem h₂)
    have hiL : ∀ B ∈ L, IntegrableOn g (Set.Icc B.1 B.2) :=
      fun B hB => hi B (Finset.mem_insert_of_mem hB)
    have hboxL : ∀ B ∈ L, ∫ x in Set.Icc B.1 B.2, g x = Φ B :=
      fun B hB => hbox B (Finset.mem_insert_of_mem hB)
    have IH' := IH haeL hiL hboxL
    rw [Finset.set_biUnion_insert, Finset.sum_insert hB₀]
    have hnull : volume (Set.Icc B₀.1 B₀.2 ∩ ⋃ B ∈ L, Set.Icc B.1 B.2) = 0 :=
      volume_inter_biUnion_boxes_null fun B hB =>
        hae B₀ (Finset.mem_insert_self B₀ L) B (Finset.mem_insert_of_mem hB)
          (fun h => hB₀ (h ▸ hB))
    have hnull' : volume ((⋃ B ∈ L, Set.Icc B.1 B.2) ∩ Set.Icc B₀.1 B₀.2) = 0 := by
      rw [Set.inter_comm]; exact hnull
    have hint : IntegrableOn g (⋃ B ∈ L, Set.Icc B.1 B.2) := integrableOn_finset_iUnion.2 hiL
    rw [Set.union_comm,
      setIntegral_union₀ hnull' measurableSet_Icc.nullMeasurableSet hint
        (hi B₀ (Finset.mem_insert_self B₀ L)),
      IH', hbox B₀ (Finset.mem_insert_self B₀ L), add_comm]

/-- **`AccountedForByStress` holds on every box complex, not only on boxes.** The hypothesis is the
repository's box-by-box predicate `Maxwell.AccountedForByStress`; the conclusion is the same
equality over any finite union of boxes with pairwise null intersections. -/
theorem accountedForByStress_biUnion {P : Vec3 → Stress} {f : Vec3 → Vec3}
    (h : AccountedForByStress P f) (L : Finset (Vec3 × Vec3))
    (hle : ∀ B ∈ L, B.1 ≤ B.2)
    (hae : ∀ B₁ ∈ L, ∀ B₂ ∈ L, B₁ ≠ B₂ →
      volume (Set.Icc B₁.1 B₁.2 ∩ Set.Icc B₂.1 B₂.2) = 0)
    (hi : ∀ B ∈ L, ∀ k, IntegrableOn (fun x => f x k) (Set.Icc B.1 B.2)) (k : Fin 3) :
    ∫ x in (⋃ B ∈ L, Set.Icc B.1 B.2), f x k
      = ∑ B ∈ L, boxSurfaceForce P B.1 B.2 k :=
  setIntegral_biUnion_boxes L hae (fun B hB => hi B hB k)
    (fun B hB => h B.1 B.2 (hle B hB) k)


/-! ## A notation trap: the norm on `Vec3` is the sup norm, not the Euclidean norm

`Vec3 = Fin 3 → ℝ` carries Mathlib's `Pi.normedAddCommGroup`, whose norm is the **sup** norm. The
Newtonian radius `r = ‖x − y‖` of Arts. 616–617 is the Euclidean one, i.e. `√(sq (x − y))`, not
Mathlib's `‖x − y‖`: `‖![3,4,0]‖ = 4`, not `5`. Decay estimates are unaffected (the two norms are
equivalent), but any claim that `1/‖x‖` is harmonic off `0` is false. -/

theorem norm_vec3_eq_sup (x : Vec3) : ‖x‖ = max (max |x 0| |x 1|) |x 2| := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (r := max (max |x 0| |x 1|) |x 2|) ?_).2 ?_
    · exact (abs_nonneg (x 0)).trans (le_max_of_le_left (le_max_of_le_left (le_refl _)))
    · intro i; fin_cases i
      · exact le_max_of_le_left (le_max_of_le_left (le_refl _))
      · exact le_max_of_le_left (le_max_of_le_right (le_refl _))
      · exact le_max_of_le_right (le_refl _)
  · have h0 := norm_le_pi_norm x 0
    have h1 := norm_le_pi_norm x 1
    have h2 := norm_le_pi_norm x 2
    simp only [Real.norm_eq_abs] at h0 h1 h2
    exact max_le (max_le h0 h1) h2

theorem norm_three_four_zero : ‖(![3, 4, 0] : Vec3)‖ = 4 := by
  rw [norm_vec3_eq_sup]; simp; norm_num

theorem norm_one_one_zero : ‖(![1, 1, 0] : Vec3)‖ = 1 := by
  rw [norm_vec3_eq_sup]; simp

end Maxwell
