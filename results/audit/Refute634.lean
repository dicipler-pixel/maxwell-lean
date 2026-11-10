/-
Independent check of one open target in `Maxwell/Statements.lean`.

`Art634KineticEnergy` is the *shape* of Treatise Art. 634 eq. (16), with the link between the
circuits and the current density `J` left out.  This file records, in Lean, that the equation is
false for data that do not satisfy that link, so it cannot be closed as it stands: the missing
link has to enter as a hypothesis.  Nothing here is part of the library; `Maxwell.lean` does not
import it.
-/
import Maxwell.Statements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Maxwell.Refute

open MeasureTheory

/-- A closed-form case of `circuitMomentum`: a straight segment from `0` to `1` along the `x`
axis, with a constant unit vector potential, has momentum `1`. -/
theorem circuitMomentum_segment :
    circuitMomentum (fun _ => ![1, 0, 0]) (fun t => ![t, 0, 0]) (fun _ => ![1, 0, 0]) = 1 := by
  simp [circuitMomentum]

/-- **The target as stated is false.**  One circuit along the `x` axis carrying current `1`, a
constant vector potential `(1,0,0)` and no current density at all: the left side is `½`, the
right side is `0`.  Maxwell's identity needs `J` to be the current that the circuits carry; with
that link absent the equation cannot hold for all data. -/
theorem art634_shape_false :
    ¬ Art634KineticEnergy (ι := Fin 1) (A := fun _ => ![1, 0, 0]) (J := fun _ => 0)
        (γ := fun _ t => ![t, 0, 0]) (γ' := fun _ _ => ![1, 0, 0]) (current := fun _ => 1) := by
  intro h
  simp only [Art634KineticEnergy, Fin.sum_univ_one, circuitMomentum_segment] at h
  norm_num at h

end Maxwell.Refute

#print axioms Maxwell.Refute.art634_shape_false
#print axioms Maxwell.Refute.circuitMomentum_segment
