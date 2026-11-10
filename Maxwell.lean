-- Root module: imports only proved modules (and the data-only `Sources`).
-- `Maxwell.Statements` (statements only) is built by the library glob but not imported here.
import Maxwell.Basic
import Maxwell.Sources
import Maxwell.Treatise.ElectrostaticStress
import Maxwell.Treatise.MagneticStress
import Maxwell.Treatise.Energy
import Maxwell.Treatise.RadiationPressure
import Maxwell.Treatise.ElectromotiveForce
import Maxwell.Treatise.VectorPotential
import Maxwell.Treatise.CircuitFlux
import Maxwell.Treatise.BoxComplex
import Maxwell.Treatise.GaugeLinearFunctional
import Maxwell.Treatise.NewtonianPotential
import Maxwell.Treatise.NewtonianPotentialC1
