# One CI line to apply by hand

The push of commit `4d80832` was rejected by GitHub:

```
! [remote rejected] (refusing to allow a GitHub App to create or update workflow
  `.github/workflows/lean.yml` without `workflows` permission)
```

The connected GitHub App has no `workflows` permission, so `.github/workflows/lean.yml` cannot be
changed through this channel. Everything else in the commit is pushed; the workflow edit is the
only thing left behind, and it is one line.

`leanchecker` steps through a hard-coded module list, so the five new modules are not replayed in
CI until this line is extended. In `.github/workflows/lean.yml`, in the step *Replay every module in
the independent kernel checker*, replace the `for m in ...` line with:

```yaml
          for m in Basic Sources Treatise.ElectrostaticStress Treatise.MagneticStress Treatise.Energy Treatise.RadiationPressure Treatise.ElectromotiveForce Treatise.VectorPotential Treatise.CircuitFlux Treatise.BoxComplex Treatise.GaugeLinearFunctional Treatise.NewtonianPotential Treatise.NewtonianPotentialC1 Statements; do
```

(The old line stopped at `Treatise.VectorPotential Statements`.) That is the only change; the rest of
the workflow is untouched. The list now matches the library's 14 modules, so a module added later
would be missed again — worth replacing it with a glob over `Maxwell/**/*.lean` at some point.
