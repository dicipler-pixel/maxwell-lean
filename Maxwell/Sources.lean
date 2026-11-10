/-
Copyright (c) 2026 Jeromie Beasley. Released under the MIT license (see LICENSE).
-/

/-!
# Source records: Maxwell's claims, hypotheses, and stated limits, in his words

Each record names the work, edition, article or section, page in the edition used, the local
OCR file under `/workspace/maxwell_reread/`, an exact quotation (checked against that file), and
a status. These are **data**, not theorems: nothing here is asserted in Lean. They exist so that
the limits Maxwell stated stay visible next to the proofs and cannot be silently upgraded.
-/

namespace Maxwell

/-- How a passage is used in this library. -/
inductive Status
  /-- A claim Maxwell makes, whether proved here, stated in `Statements`, or physical. -/
  | claim
  /-- A hypothesis Maxwell introduces or adopts (it is a hypothesis in Lean too). -/
  | hypothesis
  /-- A limit Maxwell states on his own theory. Never formalized as proved. -/
  | statedLimit
  /-- An empirical position Maxwell takes. -/
  | empirical
  /-- A model Maxwell himself calls provisional. -/
  | provisional
  deriving DecidableEq, Repr

/-- A citation to Maxwell's text. -/
structure Source where
  work : String
  edition : String
  locus : String
  page : String
  localFile : String
  quote : String
  status : Status
  deriving Repr

def treatise1873I : String := "n_electricandmagne01maxwrich.txt"
def treatise1873II : String := "n_electricandmagne02maxwrich.txt"
def treatise1881I : String := "n_treatiseonelectr01maxwrich.txt"
def sciPapersI : String := "n_scientificpapers01maxwuoft.txt"

def art107 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. I"
    locus := "Art. 107", page := "p. 127", localFile := treatise1873I
    quote := "By establishing the necessity of assuming these internal forces in the theory of an \
electric medium, we have advanced a step in that theory which will not be lost though we should \
fail in accounting for these internal forces, or in explaining the mechanism by which they can be \
maintained in air, glass, and other dielectric media."
    status := .claim }

def art111 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. I"
    locus := "Art. 111", page := "p. 132", localFile := treatise1873I
    quote := "I have not been able to make the next step, namely, to account by mechanical \
considerations for these stresses in the dielectric. I therefore leave the theory at this point, \
merely stating what are the other parts of the phenomenon of induction in dielectrics."
    status := .statedLimit }

def art645 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 645", page := "p. 257", localFile := treatise1873II
    quote := "We have asserted nothing as yet with respect to the mode in which this state of \
stress is originated and maintained in the medium. ... Any further explanation of the state of \
stress, by means of the motion of the medium or otherwise, must be regarded as a separate and \
independent part of the theory, which may stand or fall without affecting our present position."
    status := .statedLimit }

def art645_superposition : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 645", page := "p. 258", localFile := treatise1873II
    quote := "In a field in which electrostatic as well as electromagnetic action is taking place, \
we must suppose the electrostatic stress described in Part I to be superposed on the \
electromagnetic stress which we have been considering."
    status := .hypothesis }

def art644 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 644", page := "p. 257", localFile := treatise1873II
    quote := "If we adopt the theories of Ampere and Weber as to the nature of magnetic and \
diamagnetic bodies, and assume that magnetic and diamagnetic polarity are due to molecular \
electric currents, we get rid of imaginary magnetic matter, and find that everywhere m = 0"
    status := .hypothesis }

def art636 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 636", page := "p. 249", localFile := treatise1873II
    quote := "According to our hypothesis, we assume the kinetic energy to exist wherever there is \
magnetic force, that is, in general, in every part of the field. The amount of this energy per \
unit of volume is -(1/8π) S.𝔅ℌ, and this energy exists in the form of some kind of motion of the \
matter in every portion of space."
    status := .hypothesis }

def art631 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 631", page := "p. 247", localFile := treatise1873II
    quote := "Hence, the electrostatic energy of the whole field will be the same if we suppose \
that it resides in every part of the field where electrical force and electrical displacement \
occur, instead of being confined to the places where free electricity is found."
    status := .claim }

def dyn1865_s74 : Source :=
  { work := "A Dynamical Theory of the Electromagnetic Field (Phil. Trans. 155, 1865)"
    edition := "Niven (ed.), Scientific Papers, vol. I, CUP 1890, paper XXV"
    locus := "§ 74", page := "p. 564", localFile := sciPapersI
    quote := "In speaking of the Energy of the field, however, I wish to be understood literally. \
All energy is the same as mechanical energy, whether it exists in the form of motion or in that \
of elasticity, or in any other form. The energy in electromagnetic phenomena is mechanical \
energy. The only question is, Where does it reside?"
    status := .claim }

def dyn1865_s82 : Source :=
  { work := "A Dynamical Theory of the Electromagnetic Field (Phil. Trans. 155, 1865)"
    edition := "Niven (ed.), Scientific Papers, vol. I, CUP 1890, paper XXV"
    locus := "§ 82 (note on the attraction of gravitation)", page := "pp. 570–571"
    localFile := sciPapersI
    quote := "As I am unable to understand in what way a medium can possess such properties, I \
cannot go any further in this direction in searching for the cause of gravitation."
    status := .statedLimit }

def art866 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 866", page := "pp. 437–438", localFile := treatise1873II
    quote := "In fact, whenever energy is transmitted from one body to another in time, there must \
be a medium or substance in which the energy exists after it leaves one body and before it \
reaches the other"
    status := .claim }

def art549 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 549", page := "p. 181", localFile := treatise1873II
    quote := "These results shew clearly that, if the phenomena are due to momentum, the momentum \
is certainly not that of the electricity in the wire"
    status := .claim }

def art574_575 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Arts. 574–575", page := "pp. 200–202", localFile := treatise1873II
    quote := "As it is of great importance to determine whether any part of the kinetic energy is \
of the form T_me, consisting of products of ordinary velocities and strengths of electric \
currents, it is desirable that experiments should be made on this subject with great care."
    status := .empirical }

def art590 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 590", page := "p. 214", localFile := treatise1873II
    quote := "We shall therefore call it the Electrokinetic Momentum at the point (x, y, z). It is \
identical with the quantity which we investigated in Art. 405 under the name of the \
vector-potential of magnetic induction."
    status := .claim }

def dyn1865_s57_58 : Source :=
  { work := "A Dynamical Theory of the Electromagnetic Field (Phil. Trans. 155, 1865)"
    edition := "Niven (ed.), Scientific Papers, vol. I, CUP 1890, paper XXV"
    locus := "§§ 57–58", page := "pp. 555–556", localFile := sciPapersI
    quote := "(57) Let F, G, H represent the components of electromagnetic momentum at any point \
of the field, due to any system of magnets or currents. ... (58) ... if we integrate round the \
circuit, we shall get the total electromagnetic momentum of the circuit, or the number of lines \
of magnetic force which pass through it"
    status := .claim }

def art616 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 616", page := "p. 235", localFile := treatise1873II
    quote := "The quantity χ disappears from the equations (A), and it is not related to any \
physical phenomenon. If we suppose it to be zero everywhere, J will also be zero everywhere"
    status := .hypothesis }

def art377 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 377", page := "p. 4", localFile := treatise1873II
    quote := "In every Magnet the total quantity of Magnetism (reckoned algebraically) is zero."
    status := .empirical }

def art832 : Source :=
  { work := "A Treatise on Electricity and Magnetism", edition := "1st ed., Clarendon 1873, vol. II"
    locus := "Art. 832", page := "pp. 417–418 (page break not legible in the OCR)", localFile := treatise1873II
    quote := "magnetization is a phenomenon, not of large masses of iron, but of molecules, that \
is to say, of portions of the substance so small that we cannot by any mechanical method cut one \
of them in two, so as to obtain a north pole separate from a south pole."
    status := .empirical }

def physicalLines1861_provisional : Source :=
  { work := "On Physical Lines of Force (Phil. Mag. 1861–62)"
    edition := "Niven (ed.), Scientific Papers, vol. I, CUP 1890, paper XXIII"
    locus := "Part II", page := "p. 486", localFile := sciPapersI
    quote := "any one who understands the provisional and temporary character of this hypothesis"
    status := .provisional }

/-- All records, for review. -/
def allSources : List Source :=
  [art107, art111, art645, art645_superposition, art644, art636, art631, dyn1865_s74,
    dyn1865_s82, art866, art549, art574_575, art590, dyn1865_s57_58, art616, art377, art832,
    physicalLines1861_provisional]

end Maxwell
